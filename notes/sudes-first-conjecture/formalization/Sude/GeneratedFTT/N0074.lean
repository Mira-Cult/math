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
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0071

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5023 : Nat.Prime 5023 := by
  apply nodeValid_prime [2, 3, 31] ⟨5023, 3, [(2, 1), (3, 4), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_6163 : Nat.Prime 6163 := by
  apply nodeValid_prime [2, 3, 13, 79] ⟨6163, 3, [(2, 1), (3, 1), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_13399 : Nat.Prime 13399 := by
  apply nodeValid_prime [2, 3, 7, 11, 29] ⟨13399, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_13687 : Nat.Prime 13687 := by
  apply nodeValid_prime [2, 3, 2281] ⟨13687, 3, [(2, 1), (3, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2281
  · decide +kernel

theorem prime_17341 : Nat.Prime 17341 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨17341, 6, [(2, 2), (3, 1), (5, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_22907 : Nat.Prime 22907 := by
  apply nodeValid_prime [2, 13, 881] ⟨22907, 5, [(2, 1), (13, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_881
  · decide +kernel

theorem prime_23003 : Nat.Prime 23003 := by
  apply nodeValid_prime [2, 7, 31, 53] ⟨23003, 2, [(2, 1), (7, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_26959 : Nat.Prime 26959 := by
  apply nodeValid_prime [2, 3, 4493] ⟨26959, 6, [(2, 1), (3, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4493
  · decide +kernel

theorem prime_30059 : Nat.Prime 30059 := by
  apply nodeValid_prime [2, 7, 19, 113] ⟨30059, 2, [(2, 1), (7, 1), (19, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_113
  · decide +kernel

theorem prime_34231 : Nat.Prime 34231 := by
  apply nodeValid_prime [2, 3, 5, 7, 163] ⟨34231, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_163
  · decide +kernel

theorem prime_45599 : Nat.Prime 45599 := by
  apply nodeValid_prime [2, 7, 3257] ⟨45599, 7, [(2, 1), (7, 1), (3257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3257
  · decide +kernel

theorem prime_67777 : Nat.Prime 67777 := by
  apply nodeValid_prime [2, 3, 353] ⟨67777, 5, [(2, 6), (3, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353
  · decide +kernel

theorem prime_68903 : Nat.Prime 68903 := by
  apply nodeValid_prime [2, 47, 733] ⟨68903, 5, [(2, 1), (47, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_733
  · decide +kernel

theorem prime_84533 : Nat.Prime 84533 := by
  apply nodeValid_prime [2, 7, 3019] ⟨84533, 2, [(2, 2), (7, 1), (3019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3019
  · decide +kernel

theorem prime_86269 : Nat.Prime 86269 := by
  apply nodeValid_prime [2, 3, 7, 13, 79] ⟨86269, 6, [(2, 2), (3, 1), (7, 1), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_86689 : Nat.Prime 86689 := by
  apply nodeValid_prime [2, 3, 7, 43] ⟨86689, 13, [(2, 5), (3, 2), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_91463 : Nat.Prime 91463 := by
  apply nodeValid_prime [2, 7, 47, 139] ⟨91463, 5, [(2, 1), (7, 1), (47, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_139
  · decide +kernel

theorem prime_94849 : Nat.Prime 94849 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨94849, 7, [(2, 7), (3, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_99929 : Nat.Prime 99929 := by
  apply nodeValid_prime [2, 12491] ⟨99929, 3, [(2, 3), (12491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12491
  · decide +kernel

theorem prime_106619 : Nat.Prime 106619 := by
  apply nodeValid_prime [2, 53309] ⟨106619, 2, [(2, 1), (53309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53309
  · decide +kernel

theorem prime_109141 : Nat.Prime 109141 := by
  apply nodeValid_prime [2, 3, 5, 17, 107] ⟨109141, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_107
  · decide +kernel

theorem prime_110587 : Nat.Prime 110587 := by
  apply nodeValid_prime [2, 3, 7, 2633] ⟨110587, 2, [(2, 1), (3, 1), (7, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2633
  · decide +kernel

theorem prime_127711 : Nat.Prime 127711 := by
  apply nodeValid_prime [2, 3, 5, 11, 43] ⟨127711, 6, [(2, 1), (3, 3), (5, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_129671 : Nat.Prime 129671 := by
  apply nodeValid_prime [2, 5, 12967] ⟨129671, 11, [(2, 1), (5, 1), (12967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12967
  · decide +kernel

theorem prime_151379 : Nat.Prime 151379 := by
  apply nodeValid_prime [2, 75689] ⟨151379, 2, [(2, 1), (75689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_75689
  · decide +kernel

theorem prime_168977 : Nat.Prime 168977 := by
  apply nodeValid_prime [2, 59, 179] ⟨168977, 3, [(2, 4), (59, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_179
  · decide +kernel

theorem prime_182579 : Nat.Prime 182579 := by
  apply nodeValid_prime [2, 11, 43, 193] ⟨182579, 2, [(2, 1), (11, 1), (43, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_193
  · decide +kernel

theorem prime_213599 : Nat.Prime 213599 := by
  apply nodeValid_prime [2, 7, 11, 19, 73] ⟨213599, 11, [(2, 1), (7, 1), (11, 1), (19, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_73
  · decide +kernel

theorem prime_217361 : Nat.Prime 217361 := by
  apply nodeValid_prime [2, 5, 11, 13, 19] ⟨217361, 6, [(2, 4), (5, 1), (11, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_228911 : Nat.Prime 228911 := by
  apply nodeValid_prime [2, 5, 11, 2081] ⟨228911, 11, [(2, 1), (5, 1), (11, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2081
  · decide +kernel

theorem prime_235099 : Nat.Prime 235099 := by
  apply nodeValid_prime [2, 3, 37, 353] ⟨235099, 2, [(2, 1), (3, 2), (37, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_353
  · decide +kernel

theorem prime_241867 : Nat.Prime 241867 := by
  apply nodeValid_prime [2, 3, 1493] ⟨241867, 2, [(2, 1), (3, 4), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1493
  · decide +kernel

theorem prime_255841 : Nat.Prime 255841 := by
  apply nodeValid_prime [2, 3, 5, 13, 41] ⟨255841, 7, [(2, 5), (3, 1), (5, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_258031 : Nat.Prime 258031 := by
  apply nodeValid_prime [2, 3, 5, 47, 61] ⟨258031, 6, [(2, 1), (3, 2), (5, 1), (47, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_61
  · decide +kernel

theorem prime_302173 : Nat.Prime 302173 := by
  apply nodeValid_prime [2, 3, 13, 149] ⟨302173, 2, [(2, 2), (3, 1), (13, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_149
  · decide +kernel

theorem prime_375841 : Nat.Prime 375841 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨375841, 13, [(2, 5), (3, 4), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_486443 : Nat.Prime 486443 := by
  apply nodeValid_prime [2, 11, 22111] ⟨486443, 2, [(2, 1), (11, 1), (22111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_22111
  · decide +kernel

theorem prime_492601 : Nat.Prime 492601 := by
  apply nodeValid_prime [2, 3, 5, 821] ⟨492601, 23, [(2, 3), (3, 1), (5, 2), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_821
  · decide +kernel

theorem prime_499669 : Nat.Prime 499669 := by
  apply nodeValid_prime [2, 3, 13, 3203] ⟨499669, 2, [(2, 2), (3, 1), (13, 1), (3203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3203
  · decide +kernel

theorem prime_501383 : Nat.Prime 501383 := by
  apply nodeValid_prime [2, 7, 59, 607] ⟨501383, 5, [(2, 1), (7, 1), (59, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_607
  · decide +kernel

theorem prime_509123 : Nat.Prime 509123 := by
  apply nodeValid_prime [2, 83, 3067] ⟨509123, 2, [(2, 1), (83, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_3067
  · decide +kernel

theorem prime_642931 : Nat.Prime 642931 := by
  apply nodeValid_prime [2, 3, 5, 29, 739] ⟨642931, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_739
  · decide +kernel

theorem prime_689357 : Nat.Prime 689357 := by
  apply nodeValid_prime [2, 23, 59, 127] ⟨689357, 2, [(2, 2), (23, 1), (59, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
    · exact prime_127
  · decide +kernel

theorem prime_778027 : Nat.Prime 778027 := by
  apply nodeValid_prime [2, 3, 129671] ⟨778027, 2, [(2, 1), (3, 1), (129671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_129671
  · decide +kernel

theorem prime_955957 : Nat.Prime 955957 := by
  apply nodeValid_prime [2, 3, 29, 41, 67] ⟨955957, 5, [(2, 2), (3, 1), (29, 1), (41, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_41
    · exact prime_67
  · decide +kernel

theorem prime_972887 : Nat.Prime 972887 := by
  apply nodeValid_prime [2, 486443] ⟨972887, 5, [(2, 1), (486443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_486443
  · decide +kernel

theorem prime_1002767 : Nat.Prime 1002767 := by
  apply nodeValid_prime [2, 501383] ⟨1002767, 5, [(2, 1), (501383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_501383
  · decide +kernel

theorem prime_1239223 : Nat.Prime 1239223 := by
  apply nodeValid_prime [2, 3, 241, 857] ⟨1239223, 5, [(2, 1), (3, 1), (241, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_857
  · decide +kernel

theorem prime_1266799 : Nat.Prime 1266799 := by
  apply nodeValid_prime [2, 3, 13, 109, 149] ⟨1266799, 6, [(2, 1), (3, 1), (13, 1), (109, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_109
    · exact prime_149
  · decide +kernel

theorem prime_1304167 : Nat.Prime 1304167 := by
  apply nodeValid_prime [2, 3, 217361] ⟨1304167, 5, [(2, 1), (3, 1), (217361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_217361
  · decide +kernel

theorem prime_1317917 : Nat.Prime 1317917 := by
  apply nodeValid_prime [2, 19, 17341] ⟨1317917, 2, [(2, 2), (19, 1), (17341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_17341
  · decide +kernel

theorem prime_1368761 : Nat.Prime 1368761 := by
  apply nodeValid_prime [2, 5, 19, 1801] ⟨1368761, 15, [(2, 3), (5, 1), (19, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1801
  · decide +kernel

theorem prime_1506191 : Nat.Prime 1506191 := by
  apply nodeValid_prime [2, 5, 7, 21517] ⟨1506191, 7, [(2, 1), (5, 1), (7, 1), (21517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_21517
  · decide +kernel

theorem prime_1548187 : Nat.Prime 1548187 := by
  apply nodeValid_prime [2, 3, 258031] ⟨1548187, 2, [(2, 1), (3, 1), (258031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_258031
  · decide +kernel

theorem prime_1861001 : Nat.Prime 1861001 := by
  apply nodeValid_prime [2, 5, 1861] ⟨1861001, 3, [(2, 3), (5, 3), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1861
  · decide +kernel

theorem prime_1901231 : Nat.Prime 1901231 := by
  apply nodeValid_prime [2, 5, 31, 6133] ⟨1901231, 13, [(2, 1), (5, 1), (31, 1), (6133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_6133
  · decide +kernel

theorem prime_2026469 : Nat.Prime 2026469 := by
  apply nodeValid_prime [2, 17, 1753] ⟨2026469, 2, [(2, 2), (17, 2), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1753
  · decide +kernel

theorem prime_2172571 : Nat.Prime 2172571 := by
  apply nodeValid_prime [2, 3, 5, 139, 521] ⟨2172571, 2, [(2, 1), (3, 1), (5, 1), (139, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_521
  · decide +kernel

theorem prime_2195113 : Nat.Prime 2195113 := by
  apply nodeValid_prime [2, 3, 91463] ⟨2195113, 5, [(2, 3), (3, 1), (91463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_91463
  · decide +kernel

theorem prime_2711747 : Nat.Prime 2711747 := by
  apply nodeValid_prime [2, 23, 167, 353] ⟨2711747, 2, [(2, 1), (23, 1), (167, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_167
    · exact prime_353
  · decide +kernel

theorem prime_2922331 : Nat.Prime 2922331 := by
  apply nodeValid_prime [2, 3, 5, 29, 3359] ⟨2922331, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (3359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_3359
  · decide +kernel

theorem prime_3309739 : Nat.Prime 3309739 := by
  apply nodeValid_prime [2, 3, 61, 9043] ⟨3309739, 2, [(2, 1), (3, 1), (61, 1), (9043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_9043
  · decide +kernel

theorem prime_3522773 : Nat.Prime 3522773 := by
  apply nodeValid_prime [2, 11, 23, 59] ⟨3522773, 2, [(2, 2), (11, 1), (23, 1), (59, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_59
  · decide +kernel

theorem prime_3844613 : Nat.Prime 3844613 := by
  apply nodeValid_prime [2, 19, 50587] ⟨3844613, 2, [(2, 2), (19, 1), (50587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_50587
  · decide +kernel

theorem prime_4473283 : Nat.Prime 4473283 := by
  apply nodeValid_prime [2, 3, 11, 67777] ⟨4473283, 2, [(2, 1), (3, 1), (11, 1), (67777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67777
  · decide +kernel

theorem prime_5067197 : Nat.Prime 5067197 := by
  apply nodeValid_prime [2, 1266799] ⟨5067197, 2, [(2, 2), (1266799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1266799
  · decide +kernel

theorem prime_6275117 : Nat.Prime 6275117 := by
  apply nodeValid_prime [2, 113, 13883] ⟨6275117, 2, [(2, 2), (113, 1), (13883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_13883
  · decide +kernel

theorem prime_6765139 : Nat.Prime 6765139 := by
  apply nodeValid_prime [2, 3, 375841] ⟨6765139, 2, [(2, 1), (3, 2), (375841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_375841
  · decide +kernel

theorem prime_7045547 : Nat.Prime 7045547 := by
  apply nodeValid_prime [2, 3522773] ⟨7045547, 2, [(2, 1), (3522773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3522773
  · decide +kernel

theorem prime_7434989 : Nat.Prime 7434989 := by
  apply nodeValid_prime [2, 11, 168977] ⟨7434989, 2, [(2, 2), (11, 1), (168977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_168977
  · decide +kernel

theorem prime_11061989 : Nat.Prime 11061989 := by
  apply nodeValid_prime [2, 7, 23, 89, 193] ⟨11061989, 3, [(2, 2), (7, 1), (23, 1), (89, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_89
    · exact prime_193
  · decide +kernel

theorem prime_11612597 : Nat.Prime 11612597 := by
  apply nodeValid_prime [2, 211, 13759] ⟨11612597, 2, [(2, 2), (211, 1), (13759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_13759
  · decide +kernel

theorem prime_11943397 : Nat.Prime 11943397 := by
  apply nodeValid_prime [2, 3, 110587] ⟨11943397, 5, [(2, 2), (3, 3), (110587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_110587
  · decide +kernel

theorem prime_14869979 : Nat.Prime 14869979 := by
  apply nodeValid_prime [2, 7434989] ⟨14869979, 2, [(2, 1), (7434989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7434989
  · decide +kernel

theorem prime_16260499 : Nat.Prime 16260499 := by
  apply nodeValid_prime [2, 3, 67, 97, 139] ⟨16260499, 2, [(2, 1), (3, 2), (67, 1), (97, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_97
    · exact prime_139
  · decide +kernel

theorem prime_19350259 : Nat.Prime 19350259 := by
  apply nodeValid_prime [2, 3, 43, 179, 419] ⟨19350259, 2, [(2, 1), (3, 1), (43, 1), (179, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_179
    · exact prime_419
  · decide +kernel

theorem prime_19867891 : Nat.Prime 19867891 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 2557] ⟨19867891, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (2557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_2557
  · decide +kernel

theorem prime_25801799 : Nat.Prime 25801799 := by
  apply nodeValid_prime [2, 11, 106619] ⟨25801799, 7, [(2, 1), (11, 2), (106619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_106619
  · decide +kernel

theorem prime_27060557 : Nat.Prime 27060557 := by
  apply nodeValid_prime [2, 6765139] ⟨27060557, 2, [(2, 2), (6765139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6765139
  · decide +kernel

theorem prime_27405883 : Nat.Prime 27405883 := by
  apply nodeValid_prime [2, 3, 7, 199, 1093] ⟨27405883, 3, [(2, 1), (3, 2), (7, 1), (199, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199
    · exact prime_1093
  · decide +kernel

theorem prime_33429161 : Nat.Prime 33429161 := by
  apply nodeValid_prime [2, 5, 31, 26959] ⟨33429161, 3, [(2, 3), (5, 1), (31, 1), (26959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_26959
  · decide +kernel

theorem prime_51603599 : Nat.Prime 51603599 := by
  apply nodeValid_prime [2, 25801799] ⟨51603599, 11, [(2, 1), (25801799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25801799
  · decide +kernel

theorem prime_99959939 : Nat.Prime 99959939 := by
  apply nodeValid_prime [2, 13, 3844613] ⟨99959939, 2, [(2, 1), (13, 1), (3844613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3844613
  · decide +kernel

theorem prime_109280159 : Nat.Prime 109280159 := by
  apply nodeValid_prime [2, 13, 61, 68903] ⟨109280159, 14, [(2, 1), (13, 1), (61, 1), (68903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_61
    · exact prime_68903
  · decide +kernel

theorem prime_120259889 : Nat.Prime 120259889 := by
  apply nodeValid_prime [2, 7, 41, 26189] ⟨120259889, 6, [(2, 4), (7, 1), (41, 1), (26189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_26189
  · decide +kernel

theorem prime_169093129 : Nat.Prime 169093129 := by
  apply nodeValid_prime [2, 3, 7045547] ⟨169093129, 22, [(2, 3), (3, 1), (7045547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7045547
  · decide +kernel

theorem prime_179238509 : Nat.Prime 179238509 := by
  apply nodeValid_prime [2, 37, 181, 6691] ⟨179238509, 2, [(2, 2), (37, 1), (181, 1), (6691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_181
    · exact prime_6691
  · decide +kernel

theorem prime_232935821 : Nat.Prime 232935821 := by
  apply nodeValid_prime [2, 5, 13, 19, 61, 773] ⟨232935821, 2, [(2, 2), (5, 1), (13, 1), (19, 1), (61, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_61
    · exact prime_773
  · decide +kernel

theorem prime_249110663 : Nat.Prime 249110663 := by
  apply nodeValid_prime [2, 137, 181, 5023] ⟨249110663, 5, [(2, 1), (137, 1), (181, 1), (5023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_181
    · exact prime_5023
  · decide +kernel

theorem prime_293996273 : Nat.Prime 293996273 := by
  apply nodeValid_prime [2, 19, 653, 1481] ⟨293996273, 3, [(2, 4), (19, 1), (653, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_653
    · exact prime_1481
  · decide +kernel

theorem prime_294575399 : Nat.Prime 294575399 := by
  apply nodeValid_prime [2, 13, 23, 492601] ⟨294575399, 19, [(2, 1), (13, 1), (23, 1), (492601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_492601
  · decide +kernel

theorem prime_495720133 : Nat.Prime 495720133 := by
  apply nodeValid_prime [2, 3, 31, 1117, 1193] ⟨495720133, 2, [(2, 2), (3, 1), (31, 1), (1117, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1117
    · exact prime_1193
  · decide +kernel

theorem prime_631506833 : Nat.Prime 631506833 := by
  apply nodeValid_prime [2, 11, 239, 15013] ⟨631506833, 3, [(2, 4), (11, 1), (239, 1), (15013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_15013
  · decide +kernel

theorem prime_639041831 : Nat.Prime 639041831 := by
  apply nodeValid_prime [2, 5, 7, 1304167] ⟨639041831, 7, [(2, 1), (5, 1), (7, 2), (1304167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1304167
  · decide +kernel

theorem prime_701692991 : Nat.Prime 701692991 := by
  apply nodeValid_prime [2, 5, 19, 29, 347, 367] ⟨701692991, 17, [(2, 1), (5, 1), (19, 1), (29, 1), (347, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_347
    · exact prime_367
  · decide +kernel

theorem prime_830366959 : Nat.Prime 830366959 := by
  apply nodeValid_prime [2, 3, 7253, 19081] ⟨830366959, 6, [(2, 1), (3, 1), (7253, 1), (19081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7253
    · exact prime_19081
  · decide +kernel

theorem prime_1525144843 : Nat.Prime 1525144843 := by
  apply nodeValid_prime [2, 3, 13, 2172571] ⟨1525144843, 3, [(2, 1), (3, 3), (13, 1), (2172571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2172571
  · decide +kernel

theorem prime_1763977639 : Nat.Prime 1763977639 := by
  apply nodeValid_prime [2, 3, 293996273] ⟨1763977639, 6, [(2, 1), (3, 1), (293996273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293996273
  · decide +kernel

theorem prime_2620184533 : Nat.Prime 2620184533 := by
  apply nodeValid_prime [2, 3, 7, 43, 53, 13687] ⟨2620184533, 2, [(2, 2), (3, 1), (7, 1), (43, 1), (53, 1), (13687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_53
    · exact prime_13687
  · decide +kernel

theorem prime_4066242821 : Nat.Prime 4066242821 := by
  apply nodeValid_prime [2, 5, 19, 109, 127, 773] ⟨4066242821, 2, [(2, 2), (5, 1), (19, 1), (109, 1), (127, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_109
    · exact prime_127
    · exact prime_773
  · decide +kernel

theorem prime_4683023713 : Nat.Prime 4683023713 := by
  apply nodeValid_prime [2, 3, 16260499] ⟨4683023713, 10, [(2, 5), (3, 2), (16260499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16260499
  · decide +kernel

theorem prime_5021140847 : Nat.Prime 5021140847 := by
  apply nodeValid_prime [2, 23003, 109141] ⟨5021140847, 5, [(2, 1), (23003, 1), (109141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23003
    · exact prime_109141
  · decide +kernel

theorem prime_6485264743 : Nat.Prime 6485264743 := by
  apply nodeValid_prime [2, 3, 11, 101, 972887] ⟨6485264743, 3, [(2, 1), (3, 1), (11, 1), (101, 1), (972887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_101
    · exact prime_972887
  · decide +kernel

theorem prime_8132485643 : Nat.Prime 8132485643 := by
  apply nodeValid_prime [2, 4066242821] ⟨8132485643, 2, [(2, 1), (4066242821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4066242821
  · decide +kernel

theorem prime_8310203081 : Nat.Prime 8310203081 := by
  apply nodeValid_prime [2, 5, 41, 5067197] ⟨8310203081, 3, [(2, 3), (5, 1), (41, 1), (5067197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_5067197
  · decide +kernel

theorem prime_9678879487 : Nat.Prime 9678879487 := by
  apply nodeValid_prime [2, 3, 179238509] ⟨9678879487, 5, [(2, 1), (3, 3), (179238509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179238509
  · decide +kernel

theorem prime_10016157797 : Nat.Prime 10016157797 := by
  apply nodeValid_prime [2, 10651, 235099] ⟨10016157797, 2, [(2, 2), (10651, 1), (235099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10651
    · exact prime_235099
  · decide +kernel

theorem prime_12997669423 : Nat.Prime 12997669423 := by
  apply nodeValid_prime [2, 3, 67, 107, 302173] ⟨12997669423, 3, [(2, 1), (3, 1), (67, 1), (107, 1), (302173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_107
    · exact prime_302173
  · decide +kernel

theorem prime_14287974097 : Nat.Prime 14287974097 := by
  apply nodeValid_prime [2, 3, 11, 27060557] ⟨14287974097, 5, [(2, 4), (3, 1), (11, 1), (27060557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_27060557
  · decide +kernel

theorem prime_16896970249 : Nat.Prime 16896970249 := by
  apply nodeValid_prime [2, 3, 479, 641, 2293] ⟨16896970249, 17, [(2, 3), (3, 1), (479, 1), (641, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
    · exact prime_641
    · exact prime_2293
  · decide +kernel

theorem prime_20061356603 : Nat.Prime 20061356603 := by
  apply nodeValid_prime [2, 7, 1429, 1002767] ⟨20061356603, 2, [(2, 1), (7, 1), (1429, 1), (1002767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1429
    · exact prime_1002767
  · decide +kernel

theorem prime_26839756903 : Nat.Prime 26839756903 := by
  apply nodeValid_prime [2, 3, 7, 639041831] ⟨26839756903, 3, [(2, 1), (3, 1), (7, 1), (639041831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_639041831
  · decide +kernel

theorem prime_29551494457 : Nat.Prime 29551494457 := by
  apply nodeValid_prime [2, 3, 11, 163, 228911] ⟨29551494457, 5, [(2, 3), (3, 2), (11, 1), (163, 1), (228911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_163
    · exact prime_228911
  · decide +kernel

theorem prime_43084788067 : Nat.Prime 43084788067 := by
  apply nodeValid_prime [2, 3, 17, 1409, 99929] ⟨43084788067, 2, [(2, 1), (3, 2), (17, 1), (1409, 1), (99929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1409
    · exact prime_99929
  · decide +kernel

theorem prime_49861218487 : Nat.Prime 49861218487 := by
  apply nodeValid_prime [2, 3, 8310203081] ⟨49861218487, 3, [(2, 1), (3, 1), (8310203081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8310203081
  · decide +kernel

theorem prime_61280887027 : Nat.Prime 61280887027 := by
  apply nodeValid_prime [2, 3, 6781, 1506191] ⟨61280887027, 2, [(2, 1), (3, 1), (6781, 1), (1506191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6781
    · exact prime_1506191
  · decide +kernel

theorem prime_70249206967 : Nat.Prime 70249206967 := by
  apply nodeValid_prime [2, 3, 47, 249110663] ⟨70249206967, 6, [(2, 1), (3, 1), (47, 1), (249110663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_249110663
  · decide +kernel

theorem prime_71025695753 : Nat.Prime 71025695753 := by
  apply nodeValid_prime [2, 11, 47, 71, 241867] ⟨71025695753, 5, [(2, 3), (11, 1), (47, 1), (71, 1), (241867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_71
    · exact prime_241867
  · decide +kernel

theorem prime_77823174853 : Nat.Prime 77823174853 := by
  apply nodeValid_prime [2, 3, 181, 11943397] ⟨77823174853, 2, [(2, 2), (3, 2), (181, 1), (11943397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_11943397
  · decide +kernel

theorem prime_94078807369 : Nat.Prime 94078807369 := by
  apply nodeValid_prime [2, 3, 7, 13, 67, 642931] ⟨94078807369, 11, [(2, 3), (3, 1), (7, 1), (13, 1), (67, 1), (642931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_67
    · exact prime_642931
  · decide +kernel

theorem prime_105489896167 : Nat.Prime 105489896167 := by
  apply nodeValid_prime [2, 3, 22907, 255841] ⟨105489896167, 5, [(2, 1), (3, 2), (22907, 1), (255841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22907
    · exact prime_255841
  · decide +kernel

theorem prime_143145370021 : Nat.Prime 143145370021 := by
  apply nodeValid_prime [2, 3, 5, 23, 67, 1548187] ⟨143145370021, 2, [(2, 2), (3, 1), (5, 1), (23, 1), (67, 1), (1548187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_67
    · exact prime_1548187
  · decide +kernel

theorem prime_211444626719 : Nat.Prime 211444626719 := by
  apply nodeValid_prime [2, 13, 8132485643] ⟨211444626719, 7, [(2, 1), (13, 1), (8132485643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8132485643
  · decide +kernel

theorem prime_214953176861 : Nat.Prime 214953176861 := by
  apply nodeValid_prime [2, 5, 5653, 1901231] ⟨214953176861, 2, [(2, 2), (5, 1), (5653, 1), (1901231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5653
    · exact prime_1901231
  · decide +kernel

theorem prime_284102783267 : Nat.Prime 284102783267 := by
  apply nodeValid_prime [2, 182579, 778027] ⟨284102783267, 2, [(2, 1), (182579, 1), (778027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_182579
    · exact prime_778027
  · decide +kernel

theorem prime_421495241803 : Nat.Prime 421495241803 := by
  apply nodeValid_prime [2, 3, 70249206967] ⟨421495241803, 3, [(2, 1), (3, 1), (70249206967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_70249206967
  · decide +kernel

theorem prime_424752830407 : Nat.Prime 424752830407 := by
  apply nodeValid_prime [2, 3, 34231, 689357] ⟨424752830407, 3, [(2, 1), (3, 2), (34231, 1), (689357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34231
    · exact prime_689357
  · decide +kernel

theorem prime_431319177703 : Nat.Prime 431319177703 := by
  apply nodeValid_prime [2, 3, 7, 2131, 32783] ⟨431319177703, 37, [(2, 1), (3, 2), (7, 3), (2131, 1), (32783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2131
    · exact prime_32783
  · decide +kernel

theorem prime_1682270463961 : Nat.Prime 1682270463961 := by
  apply nodeValid_prime [2, 3, 5, 31, 1861001] ⟨1682270463961, 7, [(2, 3), (3, 6), (5, 1), (31, 1), (1861001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1861001
  · decide +kernel

theorem prime_1682270464229 : Nat.Prime 1682270464229 := by
  apply nodeValid_prime [2, 28283, 14869979] ⟨1682270464229, 2, [(2, 2), (28283, 1), (14869979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_28283
    · exact prime_14869979
  · decide +kernel

theorem prime_1682270477003 : Nat.Prime 1682270477003 := by
  apply nodeValid_prime [2, 113, 641, 11612597] ⟨1682270477003, 2, [(2, 1), (113, 1), (641, 1), (11612597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_641
    · exact prime_11612597
  · decide +kernel

theorem prime_1684125030739 : Nat.Prime 1684125030739 := by
  apply nodeValid_prime [2, 3, 29, 9678879487] ⟨1684125030739, 2, [(2, 1), (3, 1), (29, 1), (9678879487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_9678879487
  · decide +kernel

theorem prime_1684125050857 : Nat.Prime 1684125050857 := by
  apply nodeValid_prime [2, 3, 113, 229, 2711747] ⟨1684125050857, 11, [(2, 3), (3, 1), (113, 1), (229, 1), (2711747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_229
    · exact prime_2711747
  · decide +kernel

theorem prime_1684125052273 : Nat.Prime 1684125052273 := by
  apply nodeValid_prime [2, 3, 13, 99959939] ⟨1684125052273, 7, [(2, 4), (3, 4), (13, 1), (99959939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_99959939
  · decide +kernel

theorem prime_1685980943447 : Nat.Prime 1685980943447 := by
  apply nodeValid_prime [2, 59, 14287974097] ⟨1685980943447, 5, [(2, 1), (59, 1), (14287974097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_14287974097
  · decide +kernel

theorem prime_1685980943503 : Nat.Prime 1685980943503 := by
  apply nodeValid_prime [2, 3, 109, 227, 571, 19889] ⟨1685980943503, 3, [(2, 1), (3, 1), (109, 1), (227, 1), (571, 1), (19889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_227
    · exact prime_571
    · exact prime_19889
  · decide +kernel

theorem prime_1685980967213 : Nat.Prime 1685980967213 := by
  apply nodeValid_prime [2, 421495241803] ⟨1685980967213, 2, [(2, 2), (421495241803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_421495241803
  · decide +kernel

theorem prime_1687838281621 : Nat.Prime 1687838281621 := by
  apply nodeValid_prime [2, 3, 5, 2543, 11061989] ⟨1687838281621, 10, [(2, 2), (3, 1), (5, 1), (2543, 1), (11061989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2543
    · exact prime_11061989
  · decide +kernel

theorem prime_1687838338673 : Nat.Prime 1687838338673 := by
  apply nodeValid_prime [2, 105489896167] ⟨1687838338673, 3, [(2, 4), (105489896167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_105489896167
  · decide +kernel

theorem prime_1687838338891 : Nat.Prime 1687838338891 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 33429161] ⟨1687838338891, 2, [(2, 1), (3, 3), (5, 1), (11, 1), (17, 1), (33429161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_33429161
  · decide +kernel

theorem prime_1689696987931 : Nat.Prime 1689696987931 := by
  apply nodeValid_prime [2, 3, 5, 7, 21001, 127711] ⟨1689696987931, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (21001, 1), (127711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_21001
    · exact prime_127711
  · decide +kernel

theorem prime_1689697024901 : Nat.Prime 1689697024901 := by
  apply nodeValid_prime [2, 5, 16896970249] ⟨1689697024901, 11, [(2, 2), (5, 2), (16896970249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16896970249
  · decide +kernel

theorem prime_1689697024991 : Nat.Prime 1689697024991 := by
  apply nodeValid_prime [2, 5, 13, 12997669423] ⟨1689697024991, 46, [(2, 1), (5, 1), (13, 1), (12997669423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_12997669423
  · decide +kernel

theorem prime_1691557012837 : Nat.Prime 1691557012837 := by
  apply nodeValid_prime [2, 3, 101, 353, 1317917] ⟨1691557012837, 2, [(2, 2), (3, 2), (101, 1), (353, 1), (1317917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_353
    · exact prime_1317917
  · decide +kernel

theorem prime_1691557013753 : Nat.Prime 1691557013753 := by
  apply nodeValid_prime [2, 211444626719] ⟨1691557013753, 3, [(2, 3), (211444626719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_211444626719
  · decide +kernel

theorem prime_1691557084523 : Nat.Prime 1691557084523 := by
  apply nodeValid_prime [2, 19, 157, 1873, 151379] ⟨1691557084523, 2, [(2, 1), (19, 1), (157, 1), (1873, 1), (151379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_157
    · exact prime_1873
    · exact prime_151379
  · decide +kernel

theorem prime_1693418532643 : Nat.Prime 1693418532643 := by
  apply nodeValid_prime [2, 3, 94078807369] ⟨1693418532643, 2, [(2, 1), (3, 2), (94078807369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_94078807369
  · decide +kernel

theorem prime_1693418533441 : Nat.Prime 1693418533441 := by
  apply nodeValid_prime [2, 3, 5, 1763977639] ⟨1693418533441, 17, [(2, 6), (3, 1), (5, 1), (1763977639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1763977639
  · decide +kernel

theorem prime_1693418566849 : Nat.Prime 1693418566849 := by
  apply nodeValid_prime [2, 3, 19, 43, 1193, 9049] ⟨1693418566849, 23, [(2, 6), (3, 1), (19, 1), (43, 1), (1193, 1), (9049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_43
    · exact prime_1193
    · exact prime_9049
  · decide +kernel

theorem prime_1695281428559 : Nat.Prime 1695281428559 := by
  apply nodeValid_prime [2, 17, 49861218487] ⟨1695281428559, 11, [(2, 1), (17, 1), (49861218487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_49861218487
  · decide +kernel

theorem prime_1695281434349 : Nat.Prime 1695281434349 := by
  apply nodeValid_prime [2, 43, 191, 51603599] ⟨1695281434349, 2, [(2, 2), (43, 1), (191, 1), (51603599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_191
    · exact prime_51603599
  · decide +kernel

theorem prime_1695281436053 : Nat.Prime 1695281436053 := by
  apply nodeValid_prime [2, 23, 86269, 213599] ⟨1695281436053, 2, [(2, 2), (23, 1), (86269, 1), (213599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_86269
    · exact prime_213599
  · decide +kernel

theorem prime_1697145606287 : Nat.Prime 1697145606287 := by
  apply nodeValid_prime [2, 13, 5021140847] ⟨1697145606287, 5, [(2, 1), (13, 2), (5021140847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5021140847
  · decide +kernel

theorem prime_1697145606509 : Nat.Prime 1697145606509 := by
  apply nodeValid_prime [2, 11, 31, 311, 401, 907] ⟨1697145606509, 3, [(2, 2), (11, 2), (31, 1), (311, 1), (401, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_311
    · exact prime_401
    · exact prime_907
  · decide +kernel

theorem prime_1697145677069 : Nat.Prime 1697145677069 := by
  apply nodeValid_prime [2, 94849, 4473283] ⟨1697145677069, 2, [(2, 2), (94849, 1), (4473283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_94849
    · exact prime_4473283
  · decide +kernel

theorem prime_1699011321629 : Nat.Prime 1699011321629 := by
  apply nodeValid_prime [2, 424752830407] ⟨1699011321629, 2, [(2, 2), (424752830407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_424752830407
  · decide +kernel

theorem prime_1699011352963 : Nat.Prime 1699011352963 := by
  apply nodeValid_prime [2, 3, 7, 11, 29, 103, 45599] ⟨1699011352963, 2, [(2, 1), (3, 4), (7, 1), (11, 1), (29, 1), (103, 1), (45599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_103
    · exact prime_45599
  · decide +kernel

theorem prime_1699011355103 : Nat.Prime 1699011355103 := by
  apply nodeValid_prime [2, 557, 1525144843] ⟨1699011355103, 5, [(2, 1), (557, 1), (1525144843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_557
    · exact prime_1525144843
  · decide +kernel

theorem prime_1700878353827 : Nat.Prime 1700878353827 := by
  apply nodeValid_prime [2, 2887, 294575399] ⟨1700878353827, 2, [(2, 1), (2887, 1), (294575399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2887
    · exact prime_294575399
  · decide +kernel

theorem prime_1700878466099 : Nat.Prime 1700878466099 := by
  apply nodeValid_prime [2, 7, 47, 103, 1873, 13399] ⟨1700878466099, 2, [(2, 1), (7, 1), (47, 1), (103, 1), (1873, 1), (13399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_103
    · exact prime_1873
    · exact prime_13399
  · decide +kernel

theorem prime_1700878467269 : Nat.Prime 1700878467269 := by
  apply nodeValid_prime [2, 227, 641, 2922331] ⟨1700878467269, 2, [(2, 2), (227, 1), (641, 1), (2922331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_641
    · exact prime_2922331
  · decide +kernel

theorem prime_1702746784573 : Nat.Prime 1702746784573 := by
  apply nodeValid_prime [2, 3, 151, 983, 955957] ⟨1702746784573, 5, [(2, 2), (3, 1), (151, 1), (983, 1), (955957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_983
    · exact prime_955957
  · decide +kernel

theorem prime_1702746824893 : Nat.Prime 1702746824893 := by
  apply nodeValid_prime [2, 3, 31, 199, 251, 91639] ⟨1702746824893, 2, [(2, 2), (3, 1), (31, 1), (199, 1), (251, 1), (91639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_199
    · exact prime_251
    · exact prime_91639
  · decide +kernel

theorem prime_1702746825491 : Nat.Prime 1702746825491 := by
  apply nodeValid_prime [2, 5, 17, 10016157797] ⟨1702746825491, 2, [(2, 1), (5, 1), (17, 1), (10016157797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_10016157797
  · decide +kernel

theorem prime_1704616624093 : Nat.Prime 1704616624093 := by
  apply nodeValid_prime [2, 3, 59, 1759, 1368761] ⟨1704616624093, 5, [(2, 2), (3, 1), (59, 1), (1759, 1), (1368761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_1759
    · exact prime_1368761
  · decide +kernel

theorem prime_1704616698073 : Nat.Prime 1704616698073 := by
  apply nodeValid_prime [2, 3, 71025695753] ⟨1704616698073, 5, [(2, 3), (3, 1), (71025695753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71025695753
  · decide +kernel

theorem prime_1704616699603 : Nat.Prime 1704616699603 := by
  apply nodeValid_prime [2, 3, 284102783267] ⟨1704616699603, 5, [(2, 1), (3, 1), (284102783267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_284102783267
  · decide +kernel

theorem prime_1706487824647 : Nat.Prime 1706487824647 := by
  apply nodeValid_prime [2, 3, 11, 37, 232935821] ⟨1706487824647, 3, [(2, 1), (3, 2), (11, 1), (37, 1), (232935821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_232935821
  · decide +kernel

theorem prime_1706487824911 : Nat.Prime 1706487824911 := by
  apply nodeValid_prime [2, 3, 5, 11, 43, 120259889] ⟨1706487824911, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (43, 1), (120259889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_120259889
  · decide +kernel

theorem prime_1706487857869 : Nat.Prime 1706487857869 := by
  apply nodeValid_prime [2, 3, 29, 169093129] ⟨1706487857869, 6, [(2, 2), (3, 1), (29, 2), (169093129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_169093129
  · decide +kernel

theorem prime_1708360315517 : Nat.Prime 1708360315517 := by
  apply nodeValid_prime [2, 163, 2620184533] ⟨1708360315517, 2, [(2, 2), (163, 1), (2620184533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_2620184533
  · decide +kernel

theorem prime_1708360316297 : Nat.Prime 1708360316297 := by
  apply nodeValid_prime [2, 29, 14737, 499669] ⟨1708360316297, 3, [(2, 3), (29, 1), (14737, 1), (499669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_14737
    · exact prime_499669
  · decide +kernel

theorem prime_1708360475527 : Nat.Prime 1708360475527 := by
  apply nodeValid_prime [2, 3, 17, 281, 19867891] ⟨1708360475527, 6, [(2, 1), (3, 2), (17, 1), (281, 1), (19867891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_281
    · exact prime_19867891
  · decide +kernel

theorem prime_1710234458851 : Nat.Prime 1710234458851 := by
  apply nodeValid_prime [2, 3, 5, 23, 495720133] ⟨1710234458851, 2, [(2, 1), (3, 1), (5, 2), (23, 1), (495720133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_495720133
  · decide +kernel

theorem prime_1710234459613 : Nat.Prime 1710234459613 := by
  apply nodeValid_prime [2, 3, 7, 17, 197, 2026469] ⟨1710234459613, 5, [(2, 2), (3, 2), (7, 1), (17, 1), (197, 1), (2026469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_197
    · exact prime_2026469
  · decide +kernel

theorem prime_1710234488351 : Nat.Prime 1710234488351 := by
  apply nodeValid_prime [2, 5, 313, 109280159] ⟨1710234488351, 7, [(2, 1), (5, 2), (313, 1), (109280159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_313
    · exact prime_109280159
  · decide +kernel

theorem prime_1712109844091 : Nat.Prime 1712109844091 := by
  apply nodeValid_prime [2, 5, 17, 67, 269, 353, 1583] ⟨1712109844091, 2, [(2, 1), (5, 1), (17, 1), (67, 1), (269, 1), (353, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_67
    · exact prime_269
    · exact prime_353
    · exact prime_1583
  · decide +kernel

theorem prime_1712109846767 : Nat.Prime 1712109846767 := by
  apply nodeValid_prime [2, 11, 77823174853] ⟨1712109846767, 5, [(2, 1), (11, 1), (77823174853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_77823174853
  · decide +kernel

theorem prime_1712109892153 : Nat.Prime 1712109892153 := by
  apply nodeValid_prime [2, 3, 11, 6485264743] ⟨1712109892153, 5, [(2, 3), (3, 1), (11, 1), (6485264743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6485264743
  · decide +kernel

theorem prime_1713986678507 : Nat.Prime 1713986678507 := by
  apply nodeValid_prime [2, 29, 29551494457] ⟨1713986678507, 2, [(2, 1), (29, 1), (29551494457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_29551494457
  · decide +kernel

theorem prime_1713986678959 : Nat.Prime 1713986678959 := by
  apply nodeValid_prime [2, 3, 61, 4683023713] ⟨1713986678959, 3, [(2, 1), (3, 1), (61, 1), (4683023713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_4683023713
  · decide +kernel

theorem prime_1713986680423 : Nat.Prime 1713986680423 := by
  apply nodeValid_prime [2, 3, 61, 3779, 1239223] ⟨1713986680423, 3, [(2, 1), (3, 1), (61, 1), (3779, 1), (1239223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_3779
    · exact prime_1239223
  · decide +kernel

theorem prime_1715864836757 : Nat.Prime 1715864836757 := by
  apply nodeValid_prime [2, 7, 61280887027] ⟨1715864836757, 2, [(2, 2), (7, 1), (61280887027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61280887027
  · decide +kernel

theorem prime_1715864839901 : Nat.Prime 1715864839901 := by
  apply nodeValid_prime [2, 5, 29, 53, 79, 251, 563] ⟨1715864839901, 2, [(2, 2), (5, 2), (29, 1), (53, 1), (79, 1), (251, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_53
    · exact prime_79
    · exact prime_251
    · exact prime_563
  · decide +kernel

theorem prime_1715864866567 : Nat.Prime 1715864866567 := by
  apply nodeValid_prime [2, 3, 14779, 19350259] ⟨1715864866567, 23, [(2, 1), (3, 1), (14779, 1), (19350259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14779
    · exact prime_19350259
  · decide +kernel

theorem prime_1717744440253 : Nat.Prime 1717744440253 := by
  apply nodeValid_prime [2, 3, 143145370021] ⟨1717744440253, 2, [(2, 2), (3, 1), (143145370021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_143145370021
  · decide +kernel

theorem prime_1717744441793 : Nat.Prime 1717744441793 := by
  apply nodeValid_prime [2, 26839756903] ⟨1717744441793, 3, [(2, 6), (26839756903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26839756903
  · decide +kernel

theorem prime_1717744441969 : Nat.Prime 1717744441969 := by
  apply nodeValid_prime [2, 3, 17, 701692991] ⟨1717744441969, 7, [(2, 4), (3, 2), (17, 1), (701692991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_701692991
  · decide +kernel

theorem prime_1719625414889 : Nat.Prime 1719625414889 := by
  apply nodeValid_prime [2, 214953176861] ⟨1719625414889, 3, [(2, 3), (214953176861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_214953176861
  · decide +kernel

theorem prime_1719625490543 : Nat.Prime 1719625490543 := by
  apply nodeValid_prime [2, 167, 26437, 194749] ⟨1719625490543, 5, [(2, 1), (167, 1), (26437, 1), (194749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_26437
    · exact prime_194749
  · decide +kernel

theorem prime_1719625491323 : Nat.Prime 1719625491323 := by
  apply nodeValid_prime [2, 17, 467, 6163, 17573] ⟨1719625491323, 2, [(2, 1), (17, 1), (467, 1), (6163, 1), (17573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_467
    · exact prime_6163
    · exact prime_17573
  · decide +kernel

theorem prime_1721507782361 : Nat.Prime 1721507782361 := by
  apply nodeValid_prime [2, 5, 84533, 509123] ⟨1721507782361, 3, [(2, 3), (5, 1), (84533, 1), (509123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_84533
    · exact prime_509123
  · decide +kernel

theorem prime_1721507785027 : Nat.Prime 1721507785027 := by
  apply nodeValid_prime [2, 3, 86689, 3309739] ⟨1721507785027, 2, [(2, 1), (3, 1), (86689, 1), (3309739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_86689
    · exact prime_3309739
  · decide +kernel

theorem prime_1721507786641 : Nat.Prime 1721507786641 := by
  apply nodeValid_prime [2, 3, 5, 17, 4679, 30059] ⟨1721507786641, 14, [(2, 4), (3, 2), (5, 1), (17, 1), (4679, 1), (30059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_4679
    · exact prime_30059
  · decide +kernel

theorem prime_1723391522681 : Nat.Prime 1723391522681 := by
  apply nodeValid_prime [2, 5, 43084788067] ⟨1723391522681, 3, [(2, 3), (5, 1), (43084788067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43084788067
  · decide +kernel

theorem prime_1723391523241 : Nat.Prime 1723391523241 := by
  apply nodeValid_prime [2, 3, 5, 97, 167, 263, 3371] ⟨1723391523241, 7, [(2, 3), (3, 1), (5, 1), (97, 1), (167, 1), (263, 1), (3371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_167
    · exact prime_263
    · exact prime_3371
  · decide +kernel

theorem prime_1723391546573 : Nat.Prime 1723391546573 := by
  apply nodeValid_prime [2, 79, 199, 27405883] ⟨1723391546573, 2, [(2, 2), (79, 1), (199, 1), (27405883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_199
    · exact prime_27405883
  · decide +kernel

theorem prime_1725276667757 : Nat.Prime 1725276667757 := by
  apply nodeValid_prime [2, 683, 631506833] ⟨1725276667757, 2, [(2, 2), (683, 1), (631506833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_683
    · exact prime_631506833
  · decide +kernel

theorem prime_1725276667859 : Nat.Prime 1725276667859 := by
  apply nodeValid_prime [2, 43, 20061356603] ⟨1725276667859, 2, [(2, 1), (43, 1), (20061356603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_20061356603
  · decide +kernel

theorem prime_1725276710813 : Nat.Prime 1725276710813 := by
  apply nodeValid_prime [2, 431319177703] ⟨1725276710813, 2, [(2, 2), (431319177703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_431319177703
  · decide +kernel

theorem prime_1727163200887 : Nat.Prime 1727163200887 := by
  apply nodeValid_prime [2, 3, 71, 1847, 2195113] ⟨1727163200887, 3, [(2, 1), (3, 1), (71, 1), (1847, 1), (2195113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_1847
    · exact prime_2195113
  · decide +kernel

theorem prime_1727163203081 : Nat.Prime 1727163203081 := by
  apply nodeValid_prime [2, 5, 7, 983, 6275117] ⟨1727163203081, 3, [(2, 3), (5, 1), (7, 1), (983, 1), (6275117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_983
    · exact prime_6275117
  · decide +kernel

theorem prime_1727163274721 : Nat.Prime 1727163274721 := by
  apply nodeValid_prime [2, 5, 13, 830366959] ⟨1727163274721, 6, [(2, 5), (5, 1), (13, 1), (830366959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_830366959
  · decide +kernel

end Sude.Lucas.Generated
