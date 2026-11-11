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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4093 : Nat.Prime 4093 := by
  apply nodeValid_prime [2, 3, 11, 31] ⟨4093, 2, [(2, 2), (3, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_6701 : Nat.Prime 6701 := by
  apply nodeValid_prime [2, 5, 67] ⟨6701, 2, [(2, 2), (5, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
  · decide +kernel

theorem prime_7237 : Nat.Prime 7237 := by
  apply nodeValid_prime [2, 3, 67] ⟨7237, 2, [(2, 2), (3, 3), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
  · decide +kernel

theorem prime_7949 : Nat.Prime 7949 := by
  apply nodeValid_prime [2, 1987] ⟨7949, 2, [(2, 2), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1987
  · decide +kernel

theorem prime_9137 : Nat.Prime 9137 := by
  apply nodeValid_prime [2, 571] ⟨9137, 3, [(2, 4), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_571
  · decide +kernel

theorem prime_10613 : Nat.Prime 10613 := by
  apply nodeValid_prime [2, 7, 379] ⟨10613, 2, [(2, 2), (7, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_379
  · decide +kernel

theorem prime_11939 : Nat.Prime 11939 := by
  apply nodeValid_prime [2, 47, 127] ⟨11939, 2, [(2, 1), (47, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_127
  · decide +kernel

theorem prime_12823 : Nat.Prime 12823 := by
  apply nodeValid_prime [2, 3, 2137] ⟨12823, 3, [(2, 1), (3, 1), (2137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2137
  · decide +kernel

theorem prime_13037 : Nat.Prime 13037 := by
  apply nodeValid_prime [2, 3259] ⟨13037, 2, [(2, 2), (3259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3259
  · decide +kernel

theorem prime_13397 : Nat.Prime 13397 := by
  apply nodeValid_prime [2, 17, 197] ⟨13397, 2, [(2, 2), (17, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_197
  · decide +kernel

theorem prime_13709 : Nat.Prime 13709 := by
  apply nodeValid_prime [2, 23, 149] ⟨13709, 2, [(2, 2), (23, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_149
  · decide +kernel

theorem prime_14029 : Nat.Prime 14029 := by
  apply nodeValid_prime [2, 3, 7, 167] ⟨14029, 6, [(2, 2), (3, 1), (7, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_167
  · decide +kernel

theorem prime_17597 : Nat.Prime 17597 := by
  apply nodeValid_prime [2, 53, 83] ⟨17597, 2, [(2, 2), (53, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_83
  · decide +kernel

theorem prime_23879 : Nat.Prime 23879 := by
  apply nodeValid_prime [2, 11939] ⟨23879, 7, [(2, 1), (11939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11939
  · decide +kernel

theorem prime_25183 : Nat.Prime 25183 := by
  apply nodeValid_prime [2, 3, 1399] ⟨25183, 5, [(2, 1), (3, 2), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1399
  · decide +kernel

theorem prime_27211 : Nat.Prime 27211 := by
  apply nodeValid_prime [2, 3, 5, 907] ⟨27211, 10, [(2, 1), (3, 1), (5, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_907
  · decide +kernel

theorem prime_27751 : Nat.Prime 27751 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨27751, 3, [(2, 1), (3, 1), (5, 3), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_28621 : Nat.Prime 28621 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨28621, 13, [(2, 2), (3, 3), (5, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_30181 : Nat.Prime 30181 := by
  apply nodeValid_prime [2, 3, 5, 503] ⟨30181, 2, [(2, 2), (3, 1), (5, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_503
  · decide +kernel

theorem prime_30517 : Nat.Prime 30517 := by
  apply nodeValid_prime [2, 3, 2543] ⟨30517, 2, [(2, 2), (3, 1), (2543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2543
  · decide +kernel

theorem prime_33161 : Nat.Prime 33161 := by
  apply nodeValid_prime [2, 5, 829] ⟨33161, 3, [(2, 3), (5, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_829
  · decide +kernel

theorem prime_35069 : Nat.Prime 35069 := by
  apply nodeValid_prime [2, 11, 797] ⟨35069, 2, [(2, 2), (11, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_797
  · decide +kernel

theorem prime_35507 : Nat.Prime 35507 := by
  apply nodeValid_prime [2, 41, 433] ⟨35507, 2, [(2, 1), (41, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_433
  · decide +kernel

theorem prime_40559 : Nat.Prime 40559 := by
  apply nodeValid_prime [2, 7, 2897] ⟨40559, 7, [(2, 1), (7, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2897
  · decide +kernel

theorem prime_46399 : Nat.Prime 46399 := by
  apply nodeValid_prime [2, 3, 11, 19, 37] ⟨46399, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_46471 : Nat.Prime 46471 := by
  apply nodeValid_prime [2, 3, 5, 1549] ⟨46471, 3, [(2, 1), (3, 1), (5, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1549
  · decide +kernel

theorem prime_48407 : Nat.Prime 48407 := by
  apply nodeValid_prime [2, 24203] ⟨48407, 5, [(2, 1), (24203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24203
  · decide +kernel

theorem prime_51043 : Nat.Prime 51043 := by
  apply nodeValid_prime [2, 3, 47, 181] ⟨51043, 2, [(2, 1), (3, 1), (47, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_181
  · decide +kernel

theorem prime_52817 : Nat.Prime 52817 := by
  apply nodeValid_prime [2, 3301] ⟨52817, 3, [(2, 4), (3301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3301
  · decide +kernel

theorem prime_55061 : Nat.Prime 55061 := by
  apply nodeValid_prime [2, 5, 2753] ⟨55061, 2, [(2, 2), (5, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2753
  · decide +kernel

theorem prime_56269 : Nat.Prime 56269 := by
  apply nodeValid_prime [2, 3, 521] ⟨56269, 2, [(2, 2), (3, 3), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
  · decide +kernel

theorem prime_59243 : Nat.Prime 59243 := by
  apply nodeValid_prime [2, 19, 1559] ⟨59243, 2, [(2, 1), (19, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1559
  · decide +kernel

theorem prime_59377 : Nat.Prime 59377 := by
  apply nodeValid_prime [2, 3, 1237] ⟨59377, 5, [(2, 4), (3, 1), (1237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1237
  · decide +kernel

theorem prime_69221 : Nat.Prime 69221 := by
  apply nodeValid_prime [2, 5, 3461] ⟨69221, 2, [(2, 2), (5, 1), (3461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3461
  · decide +kernel

theorem prime_71069 : Nat.Prime 71069 := by
  apply nodeValid_prime [2, 109, 163] ⟨71069, 2, [(2, 2), (109, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_163
  · decide +kernel

theorem prime_73883 : Nat.Prime 73883 := by
  apply nodeValid_prime [2, 17, 41, 53] ⟨73883, 2, [(2, 1), (17, 1), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_86171 : Nat.Prime 86171 := by
  apply nodeValid_prime [2, 5, 7, 1231] ⟨86171, 7, [(2, 1), (5, 1), (7, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1231
  · decide +kernel

theorem prime_88177 : Nat.Prime 88177 := by
  apply nodeValid_prime [2, 3, 11, 167] ⟨88177, 5, [(2, 4), (3, 1), (11, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_167
  · decide +kernel

theorem prime_95339 : Nat.Prime 95339 := by
  apply nodeValid_prime [2, 73, 653] ⟨95339, 2, [(2, 1), (73, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_653
  · decide +kernel

theorem prime_110813 : Nat.Prime 110813 := by
  apply nodeValid_prime [2, 13, 2131] ⟨110813, 2, [(2, 2), (13, 1), (2131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2131
  · decide +kernel

theorem prime_121883 : Nat.Prime 121883 := by
  apply nodeValid_prime [2, 149, 409] ⟨121883, 2, [(2, 1), (149, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_409
  · decide +kernel

theorem prime_134129 : Nat.Prime 134129 := by
  apply nodeValid_prime [2, 83, 101] ⟨134129, 3, [(2, 4), (83, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_101
  · decide +kernel

theorem prime_135347 : Nat.Prime 135347 := by
  apply nodeValid_prime [2, 31, 37, 59] ⟨135347, 2, [(2, 1), (31, 1), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_146009 : Nat.Prime 146009 := by
  apply nodeValid_prime [2, 18251] ⟨146009, 3, [(2, 3), (18251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18251
  · decide +kernel

theorem prime_151813 : Nat.Prime 151813 := by
  apply nodeValid_prime [2, 3, 4217] ⟨151813, 2, [(2, 2), (3, 2), (4217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4217
  · decide +kernel

theorem prime_172343 : Nat.Prime 172343 := by
  apply nodeValid_prime [2, 86171] ⟨172343, 5, [(2, 1), (86171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_86171
  · decide +kernel

theorem prime_172663 : Nat.Prime 172663 := by
  apply nodeValid_prime [2, 3, 7, 4111] ⟨172663, 3, [(2, 1), (3, 1), (7, 1), (4111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4111
  · decide +kernel

theorem prime_182417 : Nat.Prime 182417 := by
  apply nodeValid_prime [2, 13, 877] ⟨182417, 3, [(2, 4), (13, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_877
  · decide +kernel

theorem prime_182899 : Nat.Prime 182899 := by
  apply nodeValid_prime [2, 3, 1129] ⟨182899, 10, [(2, 1), (3, 4), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1129
  · decide +kernel

theorem prime_192037 : Nat.Prime 192037 := by
  apply nodeValid_prime [2, 3, 13, 1231] ⟨192037, 2, [(2, 2), (3, 1), (13, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1231
  · decide +kernel

theorem prime_248461 : Nat.Prime 248461 := by
  apply nodeValid_prime [2, 3, 5, 41, 101] ⟨248461, 2, [(2, 2), (3, 1), (5, 1), (41, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_101
  · decide +kernel

theorem prime_268781 : Nat.Prime 268781 := by
  apply nodeValid_prime [2, 5, 89, 151] ⟨268781, 3, [(2, 2), (5, 1), (89, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_151
  · decide +kernel

theorem prime_389269 : Nat.Prime 389269 := by
  apply nodeValid_prime [2, 3, 11, 983] ⟨389269, 17, [(2, 2), (3, 2), (11, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_983
  · decide +kernel

theorem prime_493399 : Nat.Prime 493399 := by
  apply nodeValid_prime [2, 3, 9137] ⟨493399, 3, [(2, 1), (3, 3), (9137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9137
  · decide +kernel

theorem prime_506929 : Nat.Prime 506929 := by
  apply nodeValid_prime [2, 3, 59, 179] ⟨506929, 7, [(2, 4), (3, 1), (59, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_179
  · decide +kernel

theorem prime_553769 : Nat.Prime 553769 := by
  apply nodeValid_prime [2, 69221] ⟨553769, 3, [(2, 3), (69221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_69221
  · decide +kernel

theorem prime_562613 : Nat.Prime 562613 := by
  apply nodeValid_prime [2, 43, 3271] ⟨562613, 2, [(2, 2), (43, 1), (3271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_3271
  · decide +kernel

theorem prime_562691 : Nat.Prime 562691 := by
  apply nodeValid_prime [2, 5, 56269] ⟨562691, 2, [(2, 1), (5, 1), (56269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_56269
  · decide +kernel

theorem prime_615679 : Nat.Prime 615679 := by
  apply nodeValid_prime [2, 3, 7, 107, 137] ⟨615679, 3, [(2, 1), (3, 1), (7, 1), (107, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_137
  · decide +kernel

theorem prime_647039 : Nat.Prime 647039 := by
  apply nodeValid_prime [2, 7, 113, 409] ⟨647039, 7, [(2, 1), (7, 1), (113, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_409
  · decide +kernel

theorem prime_658367 : Nat.Prime 658367 := by
  apply nodeValid_prime [2, 53, 6211] ⟨658367, 5, [(2, 1), (53, 1), (6211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_6211
  · decide +kernel

theorem prime_670349 : Nat.Prime 670349 := by
  apply nodeValid_prime [2, 7, 89, 269] ⟨670349, 2, [(2, 2), (7, 1), (89, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_269
  · decide +kernel

theorem prime_1317793 : Nat.Prime 1317793 := by
  apply nodeValid_prime [2, 3, 7, 37, 53] ⟨1317793, 5, [(2, 5), (3, 1), (7, 1), (37, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_53
  · decide +kernel

theorem prime_1443053 : Nat.Prime 1443053 := by
  apply nodeValid_prime [2, 13, 27751] ⟨1443053, 2, [(2, 2), (13, 1), (27751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_27751
  · decide +kernel

theorem prime_1551383 : Nat.Prime 1551383 := by
  apply nodeValid_prime [2, 7, 110813] ⟨1551383, 7, [(2, 1), (7, 1), (110813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_110813
  · decide +kernel

theorem prime_1716103 : Nat.Prime 1716103 := by
  apply nodeValid_prime [2, 3, 95339] ⟨1716103, 3, [(2, 1), (3, 2), (95339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_95339
  · decide +kernel

theorem prime_1928501 : Nat.Prime 1928501 := by
  apply nodeValid_prime [2, 5, 7, 19, 29] ⟨1928501, 3, [(2, 2), (5, 3), (7, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_1973597 : Nat.Prime 1973597 := by
  apply nodeValid_prime [2, 493399] ⟨1973597, 2, [(2, 2), (493399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_493399
  · decide +kernel

theorem prime_1999681 : Nat.Prime 1999681 := by
  apply nodeValid_prime [2, 3, 5, 2083] ⟨1999681, 11, [(2, 6), (3, 1), (5, 1), (2083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2083
  · decide +kernel

theorem prime_2331949 : Nat.Prime 2331949 := by
  apply nodeValid_prime [2, 3, 29, 6701] ⟨2331949, 6, [(2, 2), (3, 1), (29, 1), (6701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_6701
  · decide +kernel

theorem prime_2462717 : Nat.Prime 2462717 := by
  apply nodeValid_prime [2, 615679] ⟨2462717, 2, [(2, 2), (615679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_615679
  · decide +kernel

theorem prime_3125173 : Nat.Prime 3125173 := by
  apply nodeValid_prime [2, 3, 31, 271] ⟨3125173, 5, [(2, 2), (3, 1), (31, 2), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_271
  · decide +kernel

theorem prime_3857003 : Nat.Prime 3857003 := by
  apply nodeValid_prime [2, 1928501] ⟨3857003, 2, [(2, 1), (1928501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1928501
  · decide +kernel

theorem prime_5161643 : Nat.Prime 5161643 := by
  apply nodeValid_prime [2, 17, 151813] ⟨5161643, 2, [(2, 1), (17, 1), (151813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_151813
  · decide +kernel

theorem prime_5915477 : Nat.Prime 5915477 := by
  apply nodeValid_prime [2, 7, 30181] ⟨5915477, 2, [(2, 2), (7, 2), (30181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_30181
  · decide +kernel

theorem prime_7019503 : Nat.Prime 7019503 := by
  apply nodeValid_prime [2, 3, 7, 97, 1723] ⟨7019503, 3, [(2, 1), (3, 1), (7, 1), (97, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_1723
  · decide +kernel

theorem prime_8282317 : Nat.Prime 8282317 := by
  apply nodeValid_prime [2, 3, 7, 43, 2293] ⟨8282317, 2, [(2, 2), (3, 1), (7, 1), (43, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_2293
  · decide +kernel

theorem prime_8973889 : Nat.Prime 8973889 := by
  apply nodeValid_prime [2, 3, 7, 11, 607] ⟨8973889, 13, [(2, 6), (3, 1), (7, 1), (11, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_607
  · decide +kernel

theorem prime_11152439 : Nat.Prime 11152439 := by
  apply nodeValid_prime [2, 11, 506929] ⟨11152439, 7, [(2, 1), (11, 1), (506929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_506929
  · decide +kernel

theorem prime_12500693 : Nat.Prime 12500693 := by
  apply nodeValid_prime [2, 3125173] ⟨12500693, 2, [(2, 2), (3125173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3125173
  · decide +kernel

theorem prime_14834357 : Nat.Prime 14834357 := by
  apply nodeValid_prime [2, 23, 383, 421] ⟨14834357, 2, [(2, 2), (23, 1), (383, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_383
    · exact prime_421
  · decide +kernel

theorem prime_16753631 : Nat.Prime 16753631 := by
  apply nodeValid_prime [2, 5, 19, 88177] ⟨16753631, 11, [(2, 1), (5, 1), (19, 1), (88177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_88177
  · decide +kernel

theorem prime_18006113 : Nat.Prime 18006113 := by
  apply nodeValid_prime [2, 562691] ⟨18006113, 3, [(2, 5), (562691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_562691
  · decide +kernel

theorem prime_22181629 : Nat.Prime 22181629 := by
  apply nodeValid_prime [2, 3, 7, 347, 761] ⟨22181629, 2, [(2, 2), (3, 1), (7, 1), (347, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_347
    · exact prime_761
  · decide +kernel

theorem prime_26041427 : Nat.Prime 26041427 := by
  apply nodeValid_prime [2, 31, 67, 6269] ⟨26041427, 2, [(2, 1), (31, 1), (67, 1), (6269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_67
    · exact prime_6269
  · decide +kernel

theorem prime_29468171 : Nat.Prime 29468171 := by
  apply nodeValid_prime [2, 5, 1013, 2909] ⟨29468171, 2, [(2, 1), (5, 1), (1013, 1), (2909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1013
    · exact prime_2909
  · decide +kernel

theorem prime_30803911 : Nat.Prime 30803911 := by
  apply nodeValid_prime [2, 3, 5, 43, 23879] ⟨30803911, 12, [(2, 1), (3, 1), (5, 1), (43, 1), (23879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_23879
  · decide +kernel

theorem prime_37400299 : Nat.Prime 37400299 := by
  apply nodeValid_prime [2, 3, 13, 53, 83, 109] ⟨37400299, 3, [(2, 1), (3, 1), (13, 1), (53, 1), (83, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_83
    · exact prime_109
  · decide +kernel

theorem prime_42494453 : Nat.Prime 42494453 := by
  apply nodeValid_prime [2, 7, 11, 13, 10613] ⟨42494453, 3, [(2, 2), (7, 1), (11, 1), (13, 1), (10613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_10613
  · decide +kernel

theorem prime_47323817 : Nat.Prime 47323817 := by
  apply nodeValid_prime [2, 5915477] ⟨47323817, 3, [(2, 3), (5915477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5915477
  · decide +kernel

theorem prime_47366329 : Nat.Prime 47366329 := by
  apply nodeValid_prime [2, 3, 1973597] ⟨47366329, 7, [(2, 3), (3, 1), (1973597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1973597
  · decide +kernel

theorem prime_50599273 : Nat.Prime 50599273 := by
  apply nodeValid_prime [2, 3, 1451, 1453] ⟨50599273, 5, [(2, 3), (3, 1), (1451, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
    · exact prime_1453
  · decide +kernel

theorem prime_52362773 : Nat.Prime 52362773 := by
  apply nodeValid_prime [2, 7, 11, 149, 163] ⟨52362773, 2, [(2, 2), (7, 2), (11, 1), (149, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_149
    · exact prime_163
  · decide +kernel

theorem prime_58344857 : Nat.Prime 58344857 := by
  apply nodeValid_prime [2, 37, 439, 449] ⟨58344857, 5, [(2, 3), (37, 1), (439, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_439
    · exact prime_449
  · decide +kernel

theorem prime_64998559 : Nat.Prime 64998559 := by
  apply nodeValid_prime [2, 3, 557, 2161] ⟨64998559, 3, [(2, 1), (3, 3), (557, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
    · exact prime_2161
  · decide +kernel

theorem prime_69281887 : Nat.Prime 69281887 := by
  apply nodeValid_prime [2, 3, 67, 172343] ⟨69281887, 5, [(2, 1), (3, 1), (67, 1), (172343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_172343
  · decide +kernel

theorem prime_77085401 : Nat.Prime 77085401 := by
  apply nodeValid_prime [2, 5, 7, 55061] ⟨77085401, 12, [(2, 3), (5, 2), (7, 1), (55061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_55061
  · decide +kernel

theorem prime_84393203 : Nat.Prime 84393203 := by
  apply nodeValid_prime [2, 17, 146009] ⟨84393203, 2, [(2, 1), (17, 2), (146009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_146009
  · decide +kernel

theorem prime_107686669 : Nat.Prime 107686669 := by
  apply nodeValid_prime [2, 3, 8973889] ⟨107686669, 2, [(2, 2), (3, 1), (8973889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8973889
  · decide +kernel

theorem prime_121216453 : Nat.Prime 121216453 := by
  apply nodeValid_prime [2, 3, 7, 1443053] ⟨121216453, 5, [(2, 2), (3, 1), (7, 1), (1443053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1443053
  · decide +kernel

theorem prime_173668741 : Nat.Prime 173668741 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 3109] ⟨173668741, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (19, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_3109
  · decide +kernel

theorem prime_250020073 : Nat.Prime 250020073 := by
  apply nodeValid_prime [2, 3, 47, 73883] ⟨250020073, 5, [(2, 3), (3, 2), (47, 1), (73883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_73883
  · decide +kernel

theorem prime_250303589 : Nat.Prime 250303589 := by
  apply nodeValid_prime [2, 113, 553769] ⟨250303589, 3, [(2, 2), (113, 1), (553769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_553769
  · decide +kernel

theorem prime_261436111 : Nat.Prime 261436111 := by
  apply nodeValid_prime [2, 3, 5, 13, 670349] ⟨261436111, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (670349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_670349
  · decide +kernel

theorem prime_277127549 : Nat.Prime 277127549 := by
  apply nodeValid_prime [2, 69281887] ⟨277127549, 2, [(2, 2), (69281887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_69281887
  · decide +kernel

theorem prime_466968791 : Nat.Prime 466968791 := by
  apply nodeValid_prime [2, 5, 83, 562613] ⟨466968791, 7, [(2, 1), (5, 1), (83, 1), (562613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_562613
  · decide +kernel

theorem prime_487249201 : Nat.Prime 487249201 := by
  apply nodeValid_prime [2, 3, 5, 135347] ⟨487249201, 11, [(2, 4), (3, 2), (5, 2), (135347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_135347
  · decide +kernel

theorem prime_530768863 : Nat.Prime 530768863 := by
  apply nodeValid_prime [2, 3, 13, 41, 683] ⟨530768863, 5, [(2, 1), (3, 6), (13, 1), (41, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_683
  · decide +kernel

theorem prime_838804621 : Nat.Prime 838804621 := by
  apply nodeValid_prime [2, 3, 5, 79, 271, 653] ⟨838804621, 2, [(2, 2), (3, 1), (5, 1), (79, 1), (271, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_271
    · exact prime_653
  · decide +kernel

theorem prime_933937583 : Nat.Prime 933937583 := by
  apply nodeValid_prime [2, 466968791] ⟨933937583, 5, [(2, 1), (466968791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_466968791
  · decide +kernel

theorem prime_1051303453 : Nat.Prime 1051303453 := by
  apply nodeValid_prime [2, 3, 479, 182899] ⟨1051303453, 2, [(2, 2), (3, 1), (479, 1), (182899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_479
    · exact prime_182899
  · decide +kernel

theorem prime_1165485413 : Nat.Prime 1165485413 := by
  apply nodeValid_prime [2, 7, 13, 239, 13397] ⟨1165485413, 2, [(2, 2), (7, 1), (13, 1), (239, 1), (13397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_239
    · exact prime_13397
  · decide +kernel

theorem prime_1481391539 : Nat.Prime 1481391539 := by
  apply nodeValid_prime [2, 11, 43, 197, 7949] ⟨1481391539, 2, [(2, 1), (11, 1), (43, 1), (197, 1), (7949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_197
    · exact prime_7949
  · decide +kernel

theorem prime_1735071817 : Nat.Prime 1735071817 := by
  apply nodeValid_prime [2, 3, 17, 1039, 4093] ⟨1735071817, 13, [(2, 3), (3, 1), (17, 1), (1039, 1), (4093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1039
    · exact prime_4093
  · decide +kernel

theorem prime_2370534871 : Nat.Prime 2370534871 := by
  apply nodeValid_prime [2, 3, 5, 11, 37, 149, 1303] ⟨2370534871, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (37, 1), (149, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_149
    · exact prime_1303
  · decide +kernel

theorem prime_2453703617 : Nat.Prime 2453703617 := by
  apply nodeValid_prime [2, 7, 13, 139, 433] ⟨2453703617, 3, [(2, 6), (7, 2), (13, 1), (139, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_139
    · exact prime_433
  · decide +kernel

theorem prime_2775153847 : Nat.Prime 2775153847 := by
  apply nodeValid_prime [2, 3, 37, 12500693] ⟨2775153847, 5, [(2, 1), (3, 1), (37, 1), (12500693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_12500693
  · decide +kernel

theorem prime_2861442527 : Nat.Prime 2861442527 := by
  apply nodeValid_prime [2, 5323, 268781] ⟨2861442527, 5, [(2, 1), (5323, 1), (268781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5323
    · exact prime_268781
  · decide +kernel

theorem prime_2962783079 : Nat.Prime 2962783079 := by
  apply nodeValid_prime [2, 1481391539] ⟨2962783079, 7, [(2, 1), (1481391539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1481391539
  · decide +kernel

theorem prime_5539116371 : Nat.Prime 5539116371 := by
  apply nodeValid_prime [2, 5, 277, 1999681] ⟨5539116371, 2, [(2, 1), (5, 1), (277, 1), (1999681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_277
    · exact prime_1999681
  · decide +kernel

theorem prime_17078115389 : Nat.Prime 17078115389 := by
  apply nodeValid_prime [2, 23, 31, 167, 1559] ⟨17078115389, 2, [(2, 2), (23, 2), (31, 1), (167, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_167
    · exact prime_1559
  · decide +kernel

theorem prime_17126974517 : Nat.Prime 17126974517 := by
  apply nodeValid_prime [2, 139, 30803911] ⟨17126974517, 2, [(2, 2), (139, 1), (30803911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_30803911
  · decide +kernel

theorem prime_17422109987 : Nat.Prime 17422109987 := by
  apply nodeValid_prime [2, 131, 1259, 52817] ⟨17422109987, 2, [(2, 1), (131, 1), (1259, 1), (52817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_1259
    · exact prime_52817
  · decide +kernel

theorem prime_22546260259 : Nat.Prime 22546260259 := by
  apply nodeValid_prime [2, 3, 31, 121216453] ⟨22546260259, 3, [(2, 1), (3, 1), (31, 1), (121216453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_121216453
  · decide +kernel

theorem prime_38383090769 : Nat.Prime 38383090769 := by
  apply nodeValid_prime [2, 11, 19, 283, 40559] ⟨38383090769, 3, [(2, 4), (11, 1), (19, 1), (283, 1), (40559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_283
    · exact prime_40559
  · decide +kernel

theorem prime_62173409279 : Nat.Prime 62173409279 := by
  apply nodeValid_prime [2, 179, 173668741] ⟨62173409279, 7, [(2, 1), (179, 1), (173668741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_173668741
  · decide +kernel

theorem prime_191915454109 : Nat.Prime 191915454109 := by
  apply nodeValid_prime [2, 3, 7, 103, 22181629] ⟨191915454109, 2, [(2, 2), (3, 1), (7, 1), (103, 1), (22181629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_22181629
  · decide +kernel

theorem prime_192187958959 : Nat.Prime 192187958959 := by
  apply nodeValid_prime [2, 3, 61, 58344857] ⟨192187958959, 6, [(2, 1), (3, 3), (61, 1), (58344857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_58344857
  · decide +kernel

theorem prime_745012749581 : Nat.Prime 745012749581 := by
  apply nodeValid_prime [2, 5, 11, 641, 1783, 2963] ⟨745012749581, 2, [(2, 2), (5, 1), (11, 1), (641, 1), (1783, 1), (2963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_641
    · exact prime_1783
    · exact prime_2963
  · decide +kernel

theorem prime_745012749997 : Nat.Prime 745012749997 := by
  apply nodeValid_prime [2, 3, 487, 42494453] ⟨745012749997, 2, [(2, 2), (3, 2), (487, 1), (42494453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
    · exact prime_42494453
  · decide +kernel

theorem prime_745012793111 : Nat.Prime 745012793111 := by
  apply nodeValid_prime [2, 5, 23, 13037, 248461] ⟨745012793111, 11, [(2, 1), (5, 1), (23, 1), (13037, 1), (248461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_13037
    · exact prime_248461
  · decide +kernel

theorem prime_746080881311 : Nat.Prime 746080881311 := by
  apply nodeValid_prime [2, 5, 43, 1735071817] ⟨746080881311, 17, [(2, 1), (5, 1), (43, 1), (1735071817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_1735071817
  · decide +kernel

theorem prime_746080881389 : Nat.Prime 746080881389 := by
  apply nodeValid_prime [2, 41, 71, 113, 307, 1847] ⟨746080881389, 2, [(2, 2), (41, 1), (71, 1), (113, 1), (307, 1), (1847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_71
    · exact prime_113
    · exact prime_307
    · exact prime_1847
  · decide +kernel

theorem prime_746080911349 : Nat.Prime 746080911349 := by
  apply nodeValid_prime [2, 3, 62173409279] ⟨746080911349, 2, [(2, 2), (3, 1), (62173409279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62173409279
  · decide +kernel

theorem prime_747150059729 : Nat.Prime 747150059729 := by
  apply nodeValid_prime [2, 27211, 1716103] ⟨747150059729, 3, [(2, 4), (27211, 1), (1716103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_27211
    · exact prime_1716103
  · decide +kernel

theorem prime_747150060161 : Nat.Prime 747150060161 := by
  apply nodeValid_prime [2, 5, 7, 5827, 28621] ⟨747150060161, 3, [(2, 7), (5, 1), (7, 1), (5827, 1), (28621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_5827
    · exact prime_28621
  · decide +kernel

theorem prime_747150066401 : Nat.Prime 747150066401 := by
  apply nodeValid_prime [2, 5, 933937583] ⟨747150066401, 3, [(2, 5), (5, 2), (933937583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_933937583
  · decide +kernel

theorem prime_748220261483 : Nat.Prime 748220261483 := by
  apply nodeValid_prime [2, 71, 30517, 172663] ⟨748220261483, 2, [(2, 1), (71, 1), (30517, 1), (172663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_30517
    · exact prime_172663
  · decide +kernel

theorem prime_748220264773 : Nat.Prime 748220264773 := by
  apply nodeValid_prime [2, 3, 199, 9157, 34217] ⟨748220264773, 2, [(2, 2), (3, 1), (199, 1), (9157, 1), (34217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_9157
    · exact prime_34217
  · decide +kernel

theorem prime_748220264861 : Nat.Prime 748220264861 := by
  apply nodeValid_prime [2, 5, 19, 33161, 59377] ⟨748220264861, 2, [(2, 2), (5, 1), (19, 1), (33161, 1), (59377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_33161
    · exact prime_59377
  · decide +kernel

theorem prime_749291498119 : Nat.Prime 749291498119 := by
  apply nodeValid_prime [2, 3, 16903, 2462717] ⟨749291498119, 3, [(2, 1), (3, 2), (16903, 1), (2462717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16903
    · exact prime_2462717
  · decide +kernel

theorem prime_749291538691 : Nat.Prime 749291538691 := by
  apply nodeValid_prime [2, 3, 5, 2775153847] ⟨749291538691, 10, [(2, 1), (3, 3), (5, 1), (2775153847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2775153847
  · decide +kernel

theorem prime_749291539151 : Nat.Prime 749291539151 := by
  apply nodeValid_prime [2, 5, 7, 11, 1451, 134129] ⟨749291539151, 7, [(2, 1), (5, 2), (7, 1), (11, 1), (1451, 1), (134129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_1451
    · exact prime_134129
  · decide +kernel

theorem prime_750363769541 : Nat.Prime 750363769541 := by
  apply nodeValid_prime [2, 5, 7, 11, 487249201] ⟨750363769541, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (487249201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_487249201
  · decide +kernel

theorem prime_750363848747 : Nat.Prime 750363848747 := by
  apply nodeValid_prime [2, 29, 113, 2243, 51043] ⟨750363848747, 2, [(2, 1), (29, 1), (113, 1), (2243, 1), (51043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_113
    · exact prime_2243
    · exact prime_51043
  · decide +kernel

theorem prime_750363849253 : Nat.Prime 750363849253 := by
  apply nodeValid_prime [2, 3, 17, 16229, 25183] ⟨750363849253, 2, [(2, 2), (3, 3), (17, 1), (16229, 1), (25183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_16229
    · exact prime_25183
  · decide +kernel

theorem prime_751437077117 : Nat.Prime 751437077117 := by
  apply nodeValid_prime [2, 11, 17078115389] ⟨751437077117, 2, [(2, 2), (11, 1), (17078115389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17078115389
  · decide +kernel

theorem prime_751437079513 : Nat.Prime 751437079513 := by
  apply nodeValid_prime [2, 3, 7, 53, 84393203] ⟨751437079513, 5, [(2, 3), (3, 1), (7, 1), (53, 1), (84393203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_84393203
  · decide +kernel

theorem prime_751437079733 : Nat.Prime 751437079733 := by
  apply nodeValid_prime [2, 41, 43, 1231, 86561] ⟨751437079733, 2, [(2, 2), (41, 1), (43, 1), (1231, 1), (86561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_43
    · exact prime_1231
    · exact prime_86561
  · decide +kernel

theorem prime_752511426283 : Nat.Prime 752511426283 := by
  apply nodeValid_prime [2, 3, 7, 11, 1699, 35507] ⟨752511426283, 5, [(2, 1), (3, 4), (7, 1), (11, 1), (1699, 1), (35507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1699
    · exact prime_35507
  · decide +kernel

theorem prime_752511474497 : Nat.Prime 752511474497 := by
  apply nodeValid_prime [2, 653, 18006113] ⟨752511474497, 3, [(2, 6), (653, 1), (18006113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_653
    · exact prime_18006113
  · decide +kernel

theorem prime_752511474661 : Nat.Prime 752511474661 := by
  apply nodeValid_prime [2, 3, 5, 11, 29, 101, 389269] ⟨752511474661, 6, [(2, 2), (3, 1), (5, 1), (11, 1), (29, 1), (101, 1), (389269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_101
    · exact prime_389269
  · decide +kernel

theorem prime_753586814527 : Nat.Prime 753586814527 := by
  apply nodeValid_prime [2, 3, 7, 13, 53, 26041427] ⟨753586814527, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (53, 1), (26041427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_53
    · exact prime_26041427
  · decide +kernel

theorem prime_753586878749 : Nat.Prime 753586878749 := by
  apply nodeValid_prime [2, 11, 17126974517] ⟨753586878749, 2, [(2, 2), (11, 1), (17126974517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17126974517
  · decide +kernel

theorem prime_753586880177 : Nat.Prime 753586880177 := by
  apply nodeValid_prime [2, 13, 47, 77085401] ⟨753586880177, 3, [(2, 4), (13, 1), (47, 1), (77085401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_77085401
  · decide +kernel

theorem prime_754663233061 : Nat.Prime 754663233061 := by
  apply nodeValid_prime [2, 3, 5, 11, 31, 173, 71069] ⟨754663233061, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (31, 1), (173, 1), (71069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_173
    · exact prime_71069
  · decide +kernel

theorem prime_754663233223 : Nat.Prime 754663233223 := by
  apply nodeValid_prime [2, 3, 19, 59, 37400299] ⟨754663233223, 3, [(2, 1), (3, 2), (19, 1), (59, 1), (37400299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
    · exact prime_37400299
  · decide +kernel

theorem prime_754663242253 : Nat.Prime 754663242253 := by
  apply nodeValid_prime [2, 3, 5639, 11152439] ⟨754663242253, 6, [(2, 2), (3, 1), (5639, 1), (11152439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5639
    · exact prime_11152439
  · decide +kernel

theorem prime_755740713467 : Nat.Prime 755740713467 := by
  apply nodeValid_prime [2, 12823, 29468171] ⟨755740713467, 2, [(2, 1), (12823, 1), (29468171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_12823
    · exact prime_29468171
  · decide +kernel

theorem prime_755740714037 : Nat.Prime 755740714037 := by
  apply nodeValid_prime [2, 7, 11, 2453703617] ⟨755740714037, 2, [(2, 2), (7, 1), (11, 1), (2453703617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_2453703617
  · decide +kernel

theorem prime_755740714621 : Nat.Prime 755740714621 := by
  apply nodeValid_prime [2, 3, 5, 23, 353, 1551383] ⟨755740714621, 11, [(2, 2), (3, 1), (5, 1), (23, 1), (353, 1), (1551383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_353
    · exact prime_1551383
  · decide +kernel

theorem prime_756819201181 : Nat.Prime 756819201181 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 23, 658367] ⟨756819201181, 6, [(2, 2), (3, 1), (5, 1), (7, 2), (17, 1), (23, 1), (658367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_658367
  · decide +kernel

theorem prime_756819204763 : Nat.Prime 756819204763 := by
  apply nodeValid_prime [2, 3, 2663, 47366329] ⟨756819204763, 2, [(2, 1), (3, 1), (2663, 1), (47366329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2663
    · exact prime_47366329
  · decide +kernel

theorem prime_756819225427 : Nat.Prime 756819225427 := by
  apply nodeValid_prime [2, 3, 11, 773, 14834357] ⟨756819225427, 5, [(2, 1), (3, 1), (11, 1), (773, 1), (14834357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_773
    · exact prime_14834357
  · decide +kernel

theorem prime_757898776403 : Nat.Prime 757898776403 := by
  apply nodeValid_prime [2, 7237, 52362773] ⟨757898776403, 2, [(2, 1), (7237, 1), (52362773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7237
    · exact prime_52362773
  · decide +kernel

theorem prime_757898776423 : Nat.Prime 757898776423 := by
  apply nodeValid_prime [2, 3, 17, 23, 107686669] ⟨757898776423, 3, [(2, 1), (3, 2), (17, 1), (23, 1), (107686669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_107686669
  · decide +kernel

theorem prime_757898780027 : Nat.Prime 757898780027 := by
  apply nodeValid_prime [2, 17, 47, 733, 647039] ⟨757898780027, 2, [(2, 1), (17, 1), (47, 1), (733, 1), (647039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_733
    · exact prime_647039
  · decide +kernel

theorem prime_758979335663 : Nat.Prime 758979335663 := by
  apply nodeValid_prime [2, 67, 46471, 121883] ⟨758979335663, 5, [(2, 1), (67, 1), (46471, 1), (121883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_46471
    · exact prime_121883
  · decide +kernel

theorem prime_758979337577 : Nat.Prime 758979337577 := by
  apply nodeValid_prime [2, 2423, 2791, 14029] ⟨758979337577, 3, [(2, 3), (2423, 1), (2791, 1), (14029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2423
    · exact prime_2791
    · exact prime_14029
  · decide +kernel

theorem prime_758979377047 : Nat.Prime 758979377047 := by
  apply nodeValid_prime [2, 3, 11, 47323817] ⟨758979377047, 5, [(2, 1), (3, 6), (11, 1), (47323817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47323817
  · decide +kernel

theorem prime_760061011181 : Nat.Prime 760061011181 := by
  apply nodeValid_prime [2, 5, 59, 167, 3857003] ⟨760061011181, 2, [(2, 2), (5, 1), (59, 1), (167, 1), (3857003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_167
    · exact prime_3857003
  · decide +kernel

theorem prime_760061011817 : Nat.Prime 760061011817 := by
  apply nodeValid_prime [2, 179, 530768863] ⟨760061011817, 3, [(2, 3), (179, 1), (530768863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_530768863
  · decide +kernel

theorem prime_760061021921 : Nat.Prime 760061021921 := by
  apply nodeValid_prime [2, 5, 19, 250020073] ⟨760061021921, 3, [(2, 5), (5, 1), (19, 1), (250020073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_250020073
  · decide +kernel

theorem prime_761143699879 : Nat.Prime 761143699879 := by
  apply nodeValid_prime [2, 3, 2671, 2699, 17597] ⟨761143699879, 6, [(2, 1), (3, 1), (2671, 1), (2699, 1), (17597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2671
    · exact prime_2699
    · exact prime_17597
  · decide +kernel

theorem prime_761143699973 : Nat.Prime 761143699973 := by
  apply nodeValid_prime [2, 181, 1051303453] ⟨761143699973, 2, [(2, 2), (181, 1), (1051303453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_1051303453
  · decide +kernel

theorem prime_761143712183 : Nat.Prime 761143712183 := by
  apply nodeValid_prime [2, 7, 19, 2861442527] ⟨761143712183, 7, [(2, 1), (7, 1), (19, 1), (2861442527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_2861442527
  · decide +kernel

theorem prime_762227448473 : Nat.Prime 762227448473 := by
  apply nodeValid_prime [2, 7, 269, 50599273] ⟨762227448473, 5, [(2, 3), (7, 1), (269, 1), (50599273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_269
    · exact prime_50599273
  · decide +kernel

theorem prime_762227460103 : Nat.Prime 762227460103 := by
  apply nodeValid_prime [2, 3, 109, 1165485413] ⟨762227460103, 5, [(2, 1), (3, 1), (109, 1), (1165485413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1165485413
  · decide +kernel

theorem prime_762227460331 : Nat.Prime 762227460331 := by
  apply nodeValid_prime [2, 3, 5, 7, 137, 571, 46399] ⟨762227460331, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (137, 1), (571, 1), (46399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_137
    · exact prime_571
    · exact prime_46399
  · decide +kernel

theorem prime_763312202273 : Nat.Prime 763312202273 := by
  apply nodeValid_prime [2, 53, 193, 2331949] ⟨763312202273, 3, [(2, 5), (53, 1), (193, 1), (2331949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_193
    · exact prime_2331949
  · decide +kernel

theorem prime_763312205111 : Nat.Prime 763312205111 := by
  apply nodeValid_prime [2, 5, 7, 13, 838804621] ⟨763312205111, 11, [(2, 1), (5, 1), (7, 1), (13, 1), (838804621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_838804621
  · decide +kernel

theorem prime_763312228463 : Nat.Prime 763312228463 := by
  apply nodeValid_prime [2, 7, 23, 2370534871] ⟨763312228463, 5, [(2, 1), (7, 1), (23, 1), (2370534871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_2370534871
  · decide +kernel

theorem prime_764398034383 : Nat.Prime 764398034383 := by
  apply nodeValid_prime [2, 3, 43, 2962783079] ⟨764398034383, 5, [(2, 1), (3, 1), (43, 1), (2962783079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_2962783079
  · decide +kernel

theorem prime_764398035157 : Nat.Prime 764398035157 := by
  apply nodeValid_prime [2, 3, 7, 41, 43, 5161643] ⟨764398035157, 2, [(2, 2), (3, 1), (7, 1), (41, 1), (43, 1), (5161643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_43
    · exact prime_5161643
  · decide +kernel

theorem prime_764398059199 : Nat.Prime 764398059199 := by
  apply nodeValid_prime [2, 3, 23, 5539116371] ⟨764398059199, 3, [(2, 1), (3, 1), (23, 1), (5539116371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_5539116371
  · decide +kernel

theorem prime_765484866409 : Nat.Prime 765484866409 := by
  apply nodeValid_prime [2, 3, 3851, 8282317] ⟨765484866409, 11, [(2, 3), (3, 1), (3851, 1), (8282317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3851
    · exact prime_8282317
  · decide +kernel

theorem prime_765484869013 : Nat.Prime 765484869013 := by
  apply nodeValid_prime [2, 3, 48407, 1317793] ⟨765484869013, 5, [(2, 2), (3, 1), (48407, 1), (1317793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48407
    · exact prime_1317793
  · decide +kernel

theorem prime_765484933009 : Nat.Prime 765484933009 := by
  apply nodeValid_prime [2, 3, 61, 261436111] ⟨765484933009, 7, [(2, 4), (3, 1), (61, 1), (261436111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_261436111
  · decide +kernel

theorem prime_766572839293 : Nat.Prime 766572839293 := by
  apply nodeValid_prime [2, 3, 13, 59, 101, 359, 2297] ⟨766572839293, 2, [(2, 2), (3, 1), (13, 1), (59, 1), (101, 1), (359, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
    · exact prime_101
    · exact prime_359
    · exact prime_2297
  · decide +kernel

theorem prime_766572839429 : Nat.Prime 766572839429 := by
  apply nodeValid_prime [2, 11, 17422109987] ⟨766572839429, 2, [(2, 2), (11, 1), (17422109987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17422109987
  · decide +kernel

theorem prime_766572848807 : Nat.Prime 766572848807 := by
  apply nodeValid_prime [2, 17, 22546260259] ⟨766572848807, 5, [(2, 1), (17, 1), (22546260259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_22546260259
  · decide +kernel

theorem prime_767661812761 : Nat.Prime 767661812761 := by
  apply nodeValid_prime [2, 3, 5, 35069, 182417] ⟨767661812761, 11, [(2, 3), (3, 1), (5, 1), (35069, 1), (182417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35069
    · exact prime_182417
  · decide +kernel

theorem prime_767661815381 : Nat.Prime 767661815381 := by
  apply nodeValid_prime [2, 5, 38383090769] ⟨767661815381, 2, [(2, 2), (5, 1), (38383090769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_38383090769
  · decide +kernel

theorem prime_767661816437 : Nat.Prime 767661816437 := by
  apply nodeValid_prime [2, 191915454109] ⟨767661816437, 2, [(2, 2), (191915454109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_191915454109
  · decide +kernel

theorem prime_768751820101 : Nat.Prime 768751820101 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 89, 3019] ⟨768751820101, 2, [(2, 2), (3, 2), (5, 2), (11, 1), (17, 2), (89, 1), (3019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_89
    · exact prime_3019
  · decide +kernel

theorem prime_768751820927 : Nat.Prime 768751820927 := by
  apply nodeValid_prime [2, 19, 73, 277127549] ⟨768751820927, 5, [(2, 1), (19, 1), (73, 1), (277127549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
    · exact prime_277127549
  · decide +kernel

theorem prime_768751835837 : Nat.Prime 768751835837 := by
  apply nodeValid_prime [2, 192187958959] ⟨768751835837, 2, [(2, 2), (192187958959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_192187958959
  · decide +kernel

theorem prime_769842918563 : Nat.Prime 769842918563 := by
  apply nodeValid_prime [2, 293, 6841, 192037] ⟨769842918563, 5, [(2, 1), (293, 1), (6841, 1), (192037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_6841
    · exact prime_192037
  · decide +kernel

theorem prime_769842932797 : Nat.Prime 769842932797 := by
  apply nodeValid_prime [2, 3, 7, 47, 64998559] ⟨769842932797, 14, [(2, 2), (3, 2), (7, 1), (47, 1), (64998559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_64998559
  · decide +kernel

theorem prime_769842933017 : Nat.Prime 769842933017 := by
  apply nodeValid_prime [2, 13709, 7019503] ⟨769842933017, 3, [(2, 3), (13709, 1), (7019503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13709
    · exact prime_7019503
  · decide +kernel

theorem prime_770935054121 : Nat.Prime 770935054121 := by
  apply nodeValid_prime [2, 5, 7, 11, 250303589] ⟨770935054121, 3, [(2, 3), (5, 1), (7, 1), (11, 1), (250303589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_250303589
  · decide +kernel

theorem prime_770935083301 : Nat.Prime 770935083301 := by
  apply nodeValid_prime [2, 3, 5, 19, 761, 59243] ⟨770935083301, 2, [(2, 2), (3, 2), (5, 2), (19, 1), (761, 1), (59243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_761
    · exact prime_59243
  · decide +kernel

theorem prime_770935084097 : Nat.Prime 770935084097 := by
  apply nodeValid_prime [2, 719, 16753631] ⟨770935084097, 3, [(2, 6), (719, 1), (16753631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_719
    · exact prime_16753631
  · decide +kernel

end Sude.Lucas.Generated
