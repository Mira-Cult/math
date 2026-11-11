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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0099

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4801 : Nat.Prime 4801 := by
  apply nodeValid_prime [2, 3, 5] ⟨4801, 7, [(2, 6), (3, 1), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_5843 : Nat.Prime 5843 := by
  apply nodeValid_prime [2, 23, 127] ⟨5843, 2, [(2, 1), (23, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_127
  · decide +kernel

theorem prime_11027 : Nat.Prime 11027 := by
  apply nodeValid_prime [2, 37, 149] ⟨11027, 2, [(2, 1), (37, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_149
  · decide +kernel

theorem prime_11971 : Nat.Prime 11971 := by
  apply nodeValid_prime [2, 3, 5, 7, 19] ⟨11971, 10, [(2, 1), (3, 2), (5, 1), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_13217 : Nat.Prime 13217 := by
  apply nodeValid_prime [2, 7, 59] ⟨13217, 3, [(2, 5), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_13417 : Nat.Prime 13417 := by
  apply nodeValid_prime [2, 3, 13, 43] ⟨13417, 5, [(2, 3), (3, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_17189 : Nat.Prime 17189 := by
  apply nodeValid_prime [2, 4297] ⟨17189, 2, [(2, 2), (4297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4297
  · decide +kernel

theorem prime_27281 : Nat.Prime 27281 := by
  apply nodeValid_prime [2, 5, 11, 31] ⟨27281, 6, [(2, 4), (5, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_35977 : Nat.Prime 35977 := by
  apply nodeValid_prime [2, 3, 1499] ⟨35977, 10, [(2, 3), (3, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1499
  · decide +kernel

theorem prime_36307 : Nat.Prime 36307 := by
  apply nodeValid_prime [2, 3, 2017] ⟨36307, 2, [(2, 1), (3, 2), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2017
  · decide +kernel

theorem prime_38629 : Nat.Prime 38629 := by
  apply nodeValid_prime [2, 3, 29, 37] ⟨38629, 2, [(2, 2), (3, 2), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_51871 : Nat.Prime 51871 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 19] ⟨51871, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_54881 : Nat.Prime 54881 := by
  apply nodeValid_prime [2, 5, 7] ⟨54881, 3, [(2, 5), (5, 1), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_60251 : Nat.Prime 60251 := by
  apply nodeValid_prime [2, 5, 241] ⟨60251, 6, [(2, 1), (5, 3), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_63997 : Nat.Prime 63997 := by
  apply nodeValid_prime [2, 3, 5333] ⟨63997, 2, [(2, 2), (3, 1), (5333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5333
  · decide +kernel

theorem prime_68227 : Nat.Prime 68227 := by
  apply nodeValid_prime [2, 3, 83, 137] ⟨68227, 2, [(2, 1), (3, 1), (83, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_137
  · decide +kernel

theorem prime_68389 : Nat.Prime 68389 := by
  apply nodeValid_prime [2, 3, 41, 139] ⟨68389, 2, [(2, 2), (3, 1), (41, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_139
  · decide +kernel

theorem prime_68767 : Nat.Prime 68767 := by
  apply nodeValid_prime [2, 3, 73, 157] ⟨68767, 3, [(2, 1), (3, 1), (73, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_157
  · decide +kernel

theorem prime_69001 : Nat.Prime 69001 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨69001, 19, [(2, 3), (3, 1), (5, 3), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_75793 : Nat.Prime 75793 := by
  apply nodeValid_prime [2, 3, 1579] ⟨75793, 10, [(2, 4), (3, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1579
  · decide +kernel

theorem prime_80627 : Nat.Prime 80627 := by
  apply nodeValid_prime [2, 7, 13, 443] ⟨80627, 2, [(2, 1), (7, 1), (13, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_443
  · decide +kernel

theorem prime_81619 : Nat.Prime 81619 := by
  apply nodeValid_prime [2, 3, 61, 223] ⟨81619, 3, [(2, 1), (3, 1), (61, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_223
  · decide +kernel

theorem prime_90371 : Nat.Prime 90371 := by
  apply nodeValid_prime [2, 5, 7, 1291] ⟨90371, 2, [(2, 1), (5, 1), (7, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1291
  · decide +kernel

theorem prime_92927 : Nat.Prime 92927 := by
  apply nodeValid_prime [2, 97, 479] ⟨92927, 5, [(2, 1), (97, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_479
  · decide +kernel

theorem prime_94117 : Nat.Prime 94117 := by
  apply nodeValid_prime [2, 3, 11, 23, 31] ⟨94117, 2, [(2, 2), (3, 1), (11, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_96493 : Nat.Prime 96493 := by
  apply nodeValid_prime [2, 3, 11, 17, 43] ⟨96493, 5, [(2, 2), (3, 1), (11, 1), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_102181 : Nat.Prime 102181 := by
  apply nodeValid_prime [2, 3, 5, 13, 131] ⟨102181, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_131
  · decide +kernel

theorem prime_104161 : Nat.Prime 104161 := by
  apply nodeValid_prime [2, 3, 5, 7, 31] ⟨104161, 19, [(2, 5), (3, 1), (5, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_109841 : Nat.Prime 109841 := by
  apply nodeValid_prime [2, 5, 1373] ⟨109841, 3, [(2, 4), (5, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1373
  · decide +kernel

theorem prime_120607 : Nat.Prime 120607 := by
  apply nodeValid_prime [2, 3, 20101] ⟨120607, 5, [(2, 1), (3, 1), (20101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20101
  · decide +kernel

theorem prime_121661 : Nat.Prime 121661 := by
  apply nodeValid_prime [2, 5, 7, 11, 79] ⟨121661, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_125627 : Nat.Prime 125627 := by
  apply nodeValid_prime [2, 23, 2731] ⟨125627, 2, [(2, 1), (23, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2731
  · decide +kernel

theorem prime_139033 : Nat.Prime 139033 := by
  apply nodeValid_prime [2, 3, 1931] ⟨139033, 5, [(2, 3), (3, 2), (1931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1931
  · decide +kernel

theorem prime_143653 : Nat.Prime 143653 := by
  apply nodeValid_prime [2, 3, 11971] ⟨143653, 2, [(2, 2), (3, 1), (11971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11971
  · decide +kernel

theorem prime_149417 : Nat.Prime 149417 := by
  apply nodeValid_prime [2, 19, 983] ⟨149417, 3, [(2, 3), (19, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_983
  · decide +kernel

theorem prime_151247 : Nat.Prime 151247 := by
  apply nodeValid_prime [2, 47, 1609] ⟨151247, 5, [(2, 1), (47, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1609
  · decide +kernel

theorem prime_152531 : Nat.Prime 152531 := by
  apply nodeValid_prime [2, 5, 7, 2179] ⟨152531, 2, [(2, 1), (5, 1), (7, 1), (2179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2179
  · decide +kernel

theorem prime_181711 : Nat.Prime 181711 := by
  apply nodeValid_prime [2, 3, 5, 673] ⟨181711, 3, [(2, 1), (3, 3), (5, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_673
  · decide +kernel

theorem prime_195253 : Nat.Prime 195253 := by
  apply nodeValid_prime [2, 3, 53, 307] ⟨195253, 2, [(2, 2), (3, 1), (53, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_307
  · decide +kernel

theorem prime_211199 : Nat.Prime 211199 := by
  apply nodeValid_prime [2, 13, 8123] ⟨211199, 7, [(2, 1), (13, 1), (8123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8123
  · decide +kernel

theorem prime_212209 : Nat.Prime 212209 := by
  apply nodeValid_prime [2, 3, 4421] ⟨212209, 11, [(2, 4), (3, 1), (4421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4421
  · decide +kernel

theorem prime_254249 : Nat.Prime 254249 := by
  apply nodeValid_prime [2, 61, 521] ⟨254249, 3, [(2, 3), (61, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_521
  · decide +kernel

theorem prime_273881 : Nat.Prime 273881 := by
  apply nodeValid_prime [2, 5, 41, 167] ⟨273881, 3, [(2, 3), (5, 1), (41, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_167
  · decide +kernel

theorem prime_290869 : Nat.Prime 290869 := by
  apply nodeValid_prime [2, 3, 24239] ⟨290869, 2, [(2, 2), (3, 1), (24239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24239
  · decide +kernel

theorem prime_308137 : Nat.Prime 308137 := by
  apply nodeValid_prime [2, 3, 37, 347] ⟨308137, 10, [(2, 3), (3, 1), (37, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_347
  · decide +kernel

theorem prime_318247 : Nat.Prime 318247 := by
  apply nodeValid_prime [2, 3, 29, 31, 59] ⟨318247, 3, [(2, 1), (3, 1), (29, 1), (31, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
    · exact prime_59
  · decide +kernel

theorem prime_367123 : Nat.Prime 367123 := by
  apply nodeValid_prime [2, 3, 7, 8741] ⟨367123, 5, [(2, 1), (3, 1), (7, 1), (8741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8741
  · decide +kernel

theorem prime_373567 : Nat.Prime 373567 := by
  apply nodeValid_prime [2, 3, 23, 2707] ⟨373567, 3, [(2, 1), (3, 1), (23, 1), (2707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2707
  · decide +kernel

theorem prime_463549 : Nat.Prime 463549 := by
  apply nodeValid_prime [2, 3, 38629] ⟨463549, 2, [(2, 2), (3, 1), (38629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_38629
  · decide +kernel

theorem prime_508499 : Nat.Prime 508499 := by
  apply nodeValid_prime [2, 254249] ⟨508499, 2, [(2, 1), (254249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_254249
  · decide +kernel

theorem prime_558431 : Nat.Prime 558431 := by
  apply nodeValid_prime [2, 5, 55843] ⟨558431, 22, [(2, 1), (5, 1), (55843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_55843
  · decide +kernel

theorem prime_582319 : Nat.Prime 582319 := by
  apply nodeValid_prime [2, 3, 11, 17, 173] ⟨582319, 3, [(2, 1), (3, 2), (11, 1), (17, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_173
  · decide +kernel

theorem prime_622849 : Nat.Prime 622849 := by
  apply nodeValid_prime [2, 3, 811] ⟨622849, 11, [(2, 8), (3, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
  · decide +kernel

theorem prime_712847 : Nat.Prime 712847 := by
  apply nodeValid_prime [2, 61, 5843] ⟨712847, 5, [(2, 1), (61, 1), (5843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_5843
  · decide +kernel

theorem prime_741709 : Nat.Prime 741709 := by
  apply nodeValid_prime [2, 3, 11, 1873] ⟨741709, 13, [(2, 2), (3, 2), (11, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1873
  · decide +kernel

theorem prime_1234439 : Nat.Prime 1234439 := by
  apply nodeValid_prime [2, 17, 36307] ⟨1234439, 13, [(2, 1), (17, 1), (36307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_36307
  · decide +kernel

theorem prime_1505873 : Nat.Prime 1505873 := by
  apply nodeValid_prime [2, 94117] ⟨1505873, 3, [(2, 4), (94117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_94117
  · decide +kernel

theorem prime_1535929 : Nat.Prime 1535929 := by
  apply nodeValid_prime [2, 3, 63997] ⟨1535929, 11, [(2, 3), (3, 1), (63997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63997
  · decide +kernel

theorem prime_1848823 : Nat.Prime 1848823 := by
  apply nodeValid_prime [2, 3, 308137] ⟨1848823, 3, [(2, 1), (3, 1), (308137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_308137
  · decide +kernel

theorem prime_1858541 : Nat.Prime 1858541 := by
  apply nodeValid_prime [2, 5, 92927] ⟨1858541, 2, [(2, 2), (5, 1), (92927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_92927
  · decide +kernel

theorem prime_1878257 : Nat.Prime 1878257 := by
  apply nodeValid_prime [2, 89, 1319] ⟨1878257, 3, [(2, 4), (89, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1319
  · decide +kernel

theorem prime_2090597 : Nat.Prime 2090597 := by
  apply nodeValid_prime [2, 331, 1579] ⟨2090597, 2, [(2, 2), (331, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_1579
  · decide +kernel

theorem prime_2230351 : Nat.Prime 2230351 := by
  apply nodeValid_prime [2, 3, 5, 14869] ⟨2230351, 12, [(2, 1), (3, 1), (5, 2), (14869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14869
  · decide +kernel

theorem prime_2428157 : Nat.Prime 2428157 := by
  apply nodeValid_prime [2, 23, 26393] ⟨2428157, 2, [(2, 2), (23, 1), (26393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_26393
  · decide +kernel

theorem prime_3012551 : Nat.Prime 3012551 := by
  apply nodeValid_prime [2, 5, 60251] ⟨3012551, 22, [(2, 1), (5, 2), (60251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_60251
  · decide +kernel

theorem prime_3717083 : Nat.Prime 3717083 := by
  apply nodeValid_prime [2, 1858541] ⟨3717083, 2, [(2, 1), (1858541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1858541
  · decide +kernel

theorem prime_3905119 : Nat.Prime 3905119 := by
  apply nodeValid_prime [2, 3, 7, 10331] ⟨3905119, 6, [(2, 1), (3, 3), (7, 1), (10331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10331
  · decide +kernel

theorem prime_4036691 : Nat.Prime 4036691 := by
  apply nodeValid_prime [2, 5, 7, 57667] ⟨4036691, 2, [(2, 1), (5, 1), (7, 1), (57667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_57667
  · decide +kernel

theorem prime_4092947 : Nat.Prime 4092947 := by
  apply nodeValid_prime [2, 11, 13, 1301] ⟨4092947, 5, [(2, 1), (11, 2), (13, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_1301
  · decide +kernel

theorem prime_4145849 : Nat.Prime 4145849 := by
  apply nodeValid_prime [2, 7, 101, 733] ⟨4145849, 3, [(2, 3), (7, 1), (101, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_733
  · decide +kernel

theorem prime_6131989 : Nat.Prime 6131989 := by
  apply nodeValid_prime [2, 3, 59, 2887] ⟨6131989, 2, [(2, 2), (3, 2), (59, 1), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2887
  · decide +kernel

theorem prime_6226177 : Nat.Prime 6226177 := by
  apply nodeValid_prime [2, 3, 11, 67] ⟨6226177, 5, [(2, 8), (3, 1), (11, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_7631917 : Nat.Prime 7631917 := by
  apply nodeValid_prime [2, 3, 37, 17189] ⟨7631917, 2, [(2, 2), (3, 1), (37, 1), (17189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_17189
  · decide +kernel

theorem prime_8102383 : Nat.Prime 8102383 := by
  apply nodeValid_prime [2, 3, 89, 15173] ⟨8102383, 3, [(2, 1), (3, 1), (89, 1), (15173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_15173
  · decide +kernel

theorem prime_9108133 : Nat.Prime 9108133 := by
  apply nodeValid_prime [2, 3, 11, 69001] ⟨9108133, 5, [(2, 2), (3, 1), (11, 1), (69001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_69001
  · decide +kernel

theorem prime_9732881 : Nat.Prime 9732881 := by
  apply nodeValid_prime [2, 5, 121661] ⟨9732881, 3, [(2, 4), (5, 1), (121661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_121661
  · decide +kernel

theorem prime_12509129 : Nat.Prime 12509129 := by
  apply nodeValid_prime [2, 89, 17569] ⟨12509129, 3, [(2, 3), (89, 1), (17569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_17569
  · decide +kernel

theorem prime_13477043 : Nat.Prime 13477043 := by
  apply nodeValid_prime [2, 19, 83, 4273] ⟨13477043, 2, [(2, 1), (19, 1), (83, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_83
    · exact prime_4273
  · decide +kernel

theorem prime_16799897 : Nat.Prime 16799897 := by
  apply nodeValid_prime [2, 59, 35593] ⟨16799897, 3, [(2, 3), (59, 1), (35593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_35593
  · decide +kernel

theorem prime_20057717 : Nat.Prime 20057717 := by
  apply nodeValid_prime [2, 7, 269, 2663] ⟨20057717, 2, [(2, 2), (7, 1), (269, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_269
    · exact prime_2663
  · decide +kernel

theorem prime_22918573 : Nat.Prime 22918573 := by
  apply nodeValid_prime [2, 3, 212209] ⟨22918573, 2, [(2, 2), (3, 3), (212209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_212209
  · decide +kernel

theorem prime_23454103 : Nat.Prime 23454103 := by
  apply nodeValid_prime [2, 3, 7, 558431] ⟨23454103, 3, [(2, 1), (3, 1), (7, 1), (558431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_558431
  · decide +kernel

theorem prime_24706751 : Nat.Prime 24706751 := by
  apply nodeValid_prime [2, 5, 37, 2671] ⟨24706751, 11, [(2, 1), (5, 3), (37, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_2671
  · decide +kernel

theorem prime_24904709 : Nat.Prime 24904709 := by
  apply nodeValid_prime [2, 6226177] ⟨24904709, 2, [(2, 2), (6226177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6226177
  · decide +kernel

theorem prime_26620157 : Nat.Prime 26620157 := by
  apply nodeValid_prime [2, 61, 79, 1381] ⟨26620157, 3, [(2, 2), (61, 1), (79, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_79
    · exact prime_1381
  · decide +kernel

theorem prime_44604997 : Nat.Prime 44604997 := by
  apply nodeValid_prime [2, 3, 3717083] ⟨44604997, 2, [(2, 2), (3, 1), (3717083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3717083
  · decide +kernel

theorem prime_45003521 : Nat.Prime 45003521 := by
  apply nodeValid_prime [2, 5, 35159] ⟨45003521, 3, [(2, 8), (5, 1), (35159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_35159
  · decide +kernel

theorem prime_50608013 : Nat.Prime 50608013 := by
  apply nodeValid_prime [2, 7, 13, 139033] ⟨50608013, 2, [(2, 2), (7, 1), (13, 1), (139033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_139033
  · decide +kernel

theorem prime_96401633 : Nat.Prime 96401633 := by
  apply nodeValid_prime [2, 3012551] ⟨96401633, 3, [(2, 5), (3012551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3012551
  · decide +kernel

theorem prime_105475637 : Nat.Prime 105475637 := by
  apply nodeValid_prime [2, 7, 359, 1499] ⟨105475637, 2, [(2, 2), (7, 2), (359, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_359
    · exact prime_1499
  · decide +kernel

theorem prime_109202701 : Nat.Prime 109202701 := by
  apply nodeValid_prime [2, 3, 5, 137, 2657] ⟨109202701, 2, [(2, 2), (3, 1), (5, 2), (137, 1), (2657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_2657
  · decide +kernel

theorem prime_122110673 : Nat.Prime 122110673 := by
  apply nodeValid_prime [2, 7631917] ⟨122110673, 3, [(2, 4), (7631917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7631917
  · decide +kernel

theorem prime_129417611 : Nat.Prime 129417611 := by
  apply nodeValid_prime [2, 5, 7, 1848823] ⟨129417611, 6, [(2, 1), (5, 1), (7, 1), (1848823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1848823
  · decide +kernel

theorem prime_153383473 : Nat.Prime 153383473 := by
  apply nodeValid_prime [2, 3, 11, 8803] ⟨153383473, 7, [(2, 4), (3, 2), (11, 2), (8803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_8803
  · decide +kernel

theorem prime_176043937 : Nat.Prime 176043937 := by
  apply nodeValid_prime [2, 3, 191, 9601] ⟨176043937, 5, [(2, 5), (3, 1), (191, 1), (9601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_9601
  · decide +kernel

theorem prime_218151751 : Nat.Prime 218151751 := by
  apply nodeValid_prime [2, 3, 5, 290869] ⟨218151751, 6, [(2, 1), (3, 1), (5, 3), (290869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_290869
  · decide +kernel

theorem prime_258835223 : Nat.Prime 258835223 := by
  apply nodeValid_prime [2, 129417611] ⟨258835223, 5, [(2, 1), (129417611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_129417611
  · decide +kernel

theorem prime_265153561 : Nat.Prime 265153561 := by
  apply nodeValid_prime [2, 3, 5, 7, 41, 7699] ⟨265153561, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (41, 1), (7699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_7699
  · decide +kernel

theorem prime_315990341 : Nat.Prime 315990341 := by
  apply nodeValid_prime [2, 5, 131, 120607] ⟨315990341, 2, [(2, 2), (5, 1), (131, 1), (120607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_120607
  · decide +kernel

theorem prime_418323877 : Nat.Prime 418323877 := by
  apply nodeValid_prime [2, 3, 47, 741709] ⟨418323877, 2, [(2, 2), (3, 1), (47, 1), (741709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_741709
  · decide +kernel

theorem prime_480858613 : Nat.Prime 480858613 := by
  apply nodeValid_prime [2, 3, 13, 19, 53, 3061] ⟨480858613, 5, [(2, 2), (3, 1), (13, 1), (19, 1), (53, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_53
    · exact prime_3061
  · decide +kernel

theorem prime_552691859 : Nat.Prime 552691859 := by
  apply nodeValid_prime [2, 1009, 273881] ⟨552691859, 2, [(2, 1), (1009, 1), (273881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1009
    · exact prime_273881
  · decide +kernel

theorem prime_686826457 : Nat.Prime 686826457 := by
  apply nodeValid_prime [2, 3, 1049, 27281] ⟨686826457, 5, [(2, 3), (3, 1), (1049, 1), (27281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1049
    · exact prime_27281
  · decide +kernel

theorem prime_779231483 : Nat.Prime 779231483 := by
  apply nodeValid_prime [2, 17, 22918573] ⟨779231483, 2, [(2, 1), (17, 1), (22918573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_22918573
  · decide +kernel

theorem prime_1155591079 : Nat.Prime 1155591079 := by
  apply nodeValid_prime [2, 3, 1289, 149417] ⟨1155591079, 3, [(2, 1), (3, 1), (1289, 1), (149417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1289
    · exact prime_149417
  · decide +kernel

theorem prime_1189495343 : Nat.Prime 1189495343 := by
  apply nodeValid_prime [2, 7, 19, 59, 75793] ⟨1189495343, 5, [(2, 1), (7, 1), (19, 1), (59, 1), (75793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_59
    · exact prime_75793
  · decide +kernel

theorem prime_1575426659 : Nat.Prime 1575426659 := by
  apply nodeValid_prime [2, 13, 593, 102181] ⟨1575426659, 2, [(2, 1), (13, 1), (593, 1), (102181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_593
    · exact prime_102181
  · decide +kernel

theorem prime_2378990687 : Nat.Prime 2378990687 := by
  apply nodeValid_prime [2, 1189495343] ⟨2378990687, 5, [(2, 1), (1189495343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1189495343
  · decide +kernel

theorem prime_2710429759 : Nat.Prime 2710429759 := by
  apply nodeValid_prime [2, 3, 31, 2137, 2273] ⟨2710429759, 3, [(2, 1), (3, 2), (31, 1), (2137, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2137
    · exact prime_2273
  · decide +kernel

theorem prime_3469470127 : Nat.Prime 3469470127 := by
  apply nodeValid_prime [2, 3, 17, 223, 152531] ⟨3469470127, 3, [(2, 1), (3, 1), (17, 1), (223, 1), (152531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_223
    · exact prime_152531
  · decide +kernel

theorem prime_4733621213 : Nat.Prime 4733621213 := by
  apply nodeValid_prime [2, 59, 20057717] ⟨4733621213, 2, [(2, 2), (59, 1), (20057717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_20057717
  · decide +kernel

theorem prime_26378200039 : Nat.Prime 26378200039 := by
  apply nodeValid_prime [2, 3, 73, 107, 281, 2003] ⟨26378200039, 6, [(2, 1), (3, 1), (73, 1), (107, 1), (281, 1), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_107
    · exact prime_281
    · exact prime_2003
  · decide +kernel

theorem prime_26401192747 : Nat.Prime 26401192747 := by
  apply nodeValid_prime [2, 3, 17, 258835223] ⟨26401192747, 12, [(2, 1), (3, 1), (17, 1), (258835223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_258835223
  · decide +kernel

theorem prime_34667732371 : Nat.Prime 34667732371 := by
  apply nodeValid_prime [2, 3, 5, 1155591079] ⟨34667732371, 3, [(2, 1), (3, 1), (5, 1), (1155591079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1155591079
  · decide +kernel

theorem prime_36080717081 : Nat.Prime 36080717081 := by
  apply nodeValid_prime [2, 5, 599, 1505873] ⟨36080717081, 3, [(2, 3), (5, 1), (599, 1), (1505873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_599
    · exact prime_1505873
  · decide +kernel

theorem prime_36396603853 : Nat.Prime 36396603853 := by
  apply nodeValid_prime [2, 3, 7, 37, 1531, 7649] ⟨36396603853, 6, [(2, 2), (3, 1), (7, 1), (37, 1), (1531, 1), (7649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_1531
    · exact prime_7649
  · decide +kernel

theorem prime_53791056937 : Nat.Prime 53791056937 := by
  apply nodeValid_prime [2, 3, 4801, 51871] ⟨53791056937, 5, [(2, 3), (3, 3), (4801, 1), (51871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4801
    · exact prime_51871
  · decide +kernel

theorem prime_55672079321 : Nat.Prime 55672079321 := by
  apply nodeValid_prime [2, 5, 11, 13, 9732881] ⟨55672079321, 7, [(2, 3), (5, 1), (11, 1), (13, 1), (9732881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_9732881
  · decide +kernel

theorem prime_63696618737 : Nat.Prime 63696618737 := by
  apply nodeValid_prime [2, 7829, 508499] ⟨63696618737, 3, [(2, 4), (7829, 1), (508499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7829
    · exact prime_508499
  · decide +kernel

theorem prime_68551889891 : Nat.Prime 68551889891 := by
  apply nodeValid_prime [2, 5, 11, 541, 617, 1867] ⟨68551889891, 6, [(2, 1), (5, 1), (11, 1), (541, 1), (617, 1), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_541
    · exact prime_617
    · exact prime_1867
  · decide +kernel

theorem prime_82254432851 : Nat.Prime 82254432851 := by
  apply nodeValid_prime [2, 5, 17, 881, 109841] ⟨82254432851, 2, [(2, 1), (5, 2), (17, 1), (881, 1), (109841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_881
    · exact prime_109841
  · decide +kernel

theorem prime_115659983027 : Nat.Prime 115659983027 := by
  apply nodeValid_prime [2, 7, 613, 13477043] ⟨115659983027, 2, [(2, 1), (7, 1), (613, 1), (13477043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_613
    · exact prime_13477043
  · decide +kernel

theorem prime_122843479721 : Nat.Prime 122843479721 := by
  apply nodeValid_prime [2, 5, 13, 113, 2090597] ⟨122843479721, 3, [(2, 3), (5, 1), (13, 1), (113, 1), (2090597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_113
    · exact prime_2090597
  · decide +kernel

theorem prime_158407156483 : Nat.Prime 158407156483 := by
  apply nodeValid_prime [2, 3, 26401192747] ⟨158407156483, 2, [(2, 1), (3, 1), (26401192747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26401192747
  · decide +kernel

theorem prime_158683342291 : Nat.Prime 158683342291 := by
  apply nodeValid_prime [2, 3, 5, 11, 480858613] ⟨158683342291, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (480858613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_480858613
  · decide +kernel

theorem prime_214037076059 : Nat.Prime 214037076059 := by
  apply nodeValid_prime [2, 13, 13217, 622849] ⟨214037076059, 2, [(2, 1), (13, 1), (13217, 1), (622849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_13217
    · exact prime_622849
  · decide +kernel

theorem prime_245686959443 : Nat.Prime 245686959443 := by
  apply nodeValid_prime [2, 122843479721] ⟨245686959443, 2, [(2, 1), (122843479721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_122843479721
  · decide +kernel

theorem prime_428074152119 : Nat.Prime 428074152119 := by
  apply nodeValid_prime [2, 214037076059] ⟨428074152119, 11, [(2, 1), (214037076059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_214037076059
  · decide +kernel

theorem prime_572267063737 : Nat.Prime 572267063737 := by
  apply nodeValid_prime [2, 3, 19, 418323877] ⟨572267063737, 7, [(2, 3), (3, 2), (19, 1), (418323877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_418323877
  · decide +kernel

theorem prime_871239403693 : Nat.Prime 871239403693 := by
  apply nodeValid_prime [2, 3, 7, 42359, 81619] ⟨871239403693, 2, [(2, 2), (3, 2), (7, 1), (42359, 1), (81619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_42359
    · exact prime_81619
  · decide +kernel

theorem prime_1715298788501 : Nat.Prime 1715298788501 := by
  apply nodeValid_prime [2, 5, 11, 43, 1063, 6823] ⟨1715298788501, 10, [(2, 2), (5, 3), (11, 1), (43, 1), (1063, 1), (6823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_1063
    · exact prime_6823
  · decide +kernel

theorem prime_3424593216721 : Nat.Prime 3424593216721 := by
  apply nodeValid_prime [2, 3, 5, 13, 179, 6131989] ⟨3424593216721, 7, [(2, 4), (3, 1), (5, 1), (13, 1), (179, 1), (6131989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_179
    · exact prime_6131989
  · decide +kernel

theorem prime_3424593216953 : Nat.Prime 3424593216953 := by
  apply nodeValid_prime [2, 428074152119] ⟨3424593216953, 3, [(2, 3), (428074152119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_428074152119
  · decide +kernel

theorem prime_3424593249673 : Nat.Prime 3424593249673 := by
  apply nodeValid_prime [2, 3, 7, 457, 44604997] ⟨3424593249673, 11, [(2, 3), (3, 1), (7, 1), (457, 1), (44604997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_457
    · exact prime_44604997
  · decide +kernel

theorem prime_3427594494551 : Nat.Prime 3427594494551 := by
  apply nodeValid_prime [2, 5, 68551889891] ⟨3427594494551, 13, [(2, 1), (5, 2), (68551889891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_68551889891
  · decide +kernel

theorem prime_3427594495397 : Nat.Prime 3427594495397 := by
  apply nodeValid_prime [2, 19, 73, 277, 2230351] ⟨3427594495397, 2, [(2, 2), (19, 1), (73, 1), (277, 1), (2230351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
    · exact prime_277
    · exact prime_2230351
  · decide +kernel

theorem prime_3427594515691 : Nat.Prime 3427594515691 := by
  apply nodeValid_prime [2, 3, 5, 73, 1019, 1535929] ⟨3427594515691, 2, [(2, 1), (3, 1), (5, 1), (73, 1), (1019, 1), (1535929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_1019
    · exact prime_1535929
  · decide +kernel

theorem prime_3430597572911 : Nat.Prime 3430597572911 := by
  apply nodeValid_prime [2, 5, 17, 28309, 712847] ⟨3430597572911, 11, [(2, 1), (5, 1), (17, 1), (28309, 1), (712847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_28309
    · exact prime_712847
  · decide +kernel

theorem prime_3430597576499 : Nat.Prime 3430597576499 := by
  apply nodeValid_prime [2, 269, 787, 8102383] ⟨3430597576499, 2, [(2, 1), (269, 1), (787, 1), (8102383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_787
    · exact prime_8102383
  · decide +kernel

theorem prime_3430597577003 : Nat.Prime 3430597577003 := by
  apply nodeValid_prime [2, 1715298788501] ⟨3430597577003, 2, [(2, 1), (1715298788501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1715298788501
  · decide +kernel

theorem prime_3433602382423 : Nat.Prime 3433602382423 := by
  apply nodeValid_prime [2, 3, 572267063737] ⟨3433602382423, 3, [(2, 1), (3, 1), (572267063737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_572267063737
  · decide +kernel

theorem prime_3433602385021 : Nat.Prime 3433602385021 := by
  apply nodeValid_prime [2, 3, 5, 37, 19183, 80627] ⟨3433602385021, 11, [(2, 2), (3, 1), (5, 1), (37, 1), (19183, 1), (80627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_19183
    · exact prime_80627
  · decide +kernel

theorem prime_3433602412241 : Nat.Prime 3433602412241 := by
  apply nodeValid_prime [2, 5, 7, 11, 13, 263, 14821] ⟨3433602412241, 3, [(2, 4), (5, 1), (7, 1), (11, 2), (13, 1), (263, 1), (14821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_263
    · exact prime_14821
  · decide +kernel

theorem prime_3436609000471 : Nat.Prime 3436609000471 := by
  apply nodeValid_prime [2, 3, 5, 1049, 109202701] ⟨3436609000471, 3, [(2, 1), (3, 1), (5, 1), (1049, 1), (109202701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1049
    · exact prime_109202701
  · decide +kernel

theorem prime_3436609000639 : Nat.Prime 3436609000639 := by
  apply nodeValid_prime [2, 3, 11, 4733621213] ⟨3436609000639, 6, [(2, 1), (3, 1), (11, 2), (4733621213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4733621213
  · decide +kernel

theorem prime_3436609028387 : Nat.Prime 3436609028387 := by
  apply nodeValid_prime [2, 17, 3797, 26620157] ⟨3436609028387, 2, [(2, 1), (17, 1), (3797, 1), (26620157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3797
    · exact prime_26620157
  · decide +kernel

theorem prime_3439617411799 : Nat.Prime 3439617411799 := by
  apply nodeValid_prime [2, 3, 63696618737] ⟨3439617411799, 6, [(2, 1), (3, 3), (63696618737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63696618737
  · decide +kernel

theorem prime_3439617411803 : Nat.Prime 3439617411803 := by
  apply nodeValid_prime [2, 11, 13, 19, 1087, 582319] ⟨3439617411803, 2, [(2, 1), (11, 1), (13, 1), (19, 1), (1087, 1), (582319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_1087
    · exact prime_582319
  · decide +kernel

theorem prime_3439617432203 : Nat.Prime 3439617432203 := by
  apply nodeValid_prime [2, 7, 245686959443] ⟨3439617432203, 5, [(2, 1), (7, 1), (245686959443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_245686959443
  · decide +kernel

theorem prime_3442627617361 : Nat.Prime 3442627617361 := by
  apply nodeValid_prime [2, 3, 5, 577, 691, 35977] ⟨3442627617361, 19, [(2, 4), (3, 1), (5, 1), (577, 1), (691, 1), (35977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_577
    · exact prime_691
    · exact prime_35977
  · decide +kernel

theorem prime_3442627643969 : Nat.Prime 3442627643969 := by
  apply nodeValid_prime [2, 53791056937] ⟨3442627643969, 3, [(2, 6), (53791056937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53791056937
  · decide +kernel

theorem prime_3442627647623 : Nat.Prime 3442627647623 := by
  apply nodeValid_prime [2, 31, 151247, 367123] ⟨3442627647623, 5, [(2, 1), (31, 1), (151247, 1), (367123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_151247
    · exact prime_367123
  · decide +kernel

theorem prime_3445639583051 : Nat.Prime 3445639583051 := by
  apply nodeValid_prime [2, 5, 7, 787, 12509129] ⟨3445639583051, 10, [(2, 1), (5, 2), (7, 1), (787, 1), (12509129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_787
    · exact prime_12509129
  · decide +kernel

theorem prime_3445639597357 : Nat.Prime 3445639597357 := by
  apply nodeValid_prime [2, 3, 11, 143653, 181711] ⟨3445639597357, 15, [(2, 2), (3, 1), (11, 1), (143653, 1), (181711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_143653
    · exact prime_181711
  · decide +kernel

theorem prime_3445639597759 : Nat.Prime 3445639597759 := by
  apply nodeValid_prime [2, 3, 37, 547, 2699, 10513] ⟨3445639597759, 3, [(2, 1), (3, 1), (37, 1), (547, 1), (2699, 1), (10513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_547
    · exact prime_2699
    · exact prime_10513
  · decide +kernel

theorem prime_3448653306239 : Nat.Prime 3448653306239 := by
  apply nodeValid_prime [2, 7, 71, 3469470127] ⟨3448653306239, 7, [(2, 1), (7, 1), (71, 1), (3469470127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_3469470127
  · decide +kernel

theorem prime_3448653306289 : Nat.Prime 3448653306289 := by
  apply nodeValid_prime [2, 3, 19, 31, 199, 612971] ⟨3448653306289, 41, [(2, 4), (3, 1), (19, 1), (31, 1), (199, 1), (612971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_199
    · exact prime_612971
  · decide +kernel

theorem prime_3448653334003 : Nat.Prime 3448653334003 := by
  apply nodeValid_prime [2, 3, 31, 68389, 90371] ⟨3448653334003, 3, [(2, 1), (3, 2), (31, 1), (68389, 1), (90371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_68389
    · exact prime_90371
  · decide +kernel

theorem prime_3451668866291 : Nat.Prime 3451668866291 := by
  apply nodeValid_prime [2, 5, 251, 7043, 195253] ⟨3451668866291, 2, [(2, 1), (5, 1), (251, 1), (7043, 1), (195253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
    · exact prime_7043
    · exact prime_195253
  · decide +kernel

theorem prime_3451668917903 : Nat.Prime 3451668917903 := by
  apply nodeValid_prime [2, 31, 55672079321] ⟨3451668917903, 5, [(2, 1), (31, 1), (55672079321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_55672079321
  · decide +kernel

theorem prime_3451668918653 : Nat.Prime 3451668918653 := by
  apply nodeValid_prime [2, 17, 59, 50608013] ⟨3451668918653, 2, [(2, 2), (17, 2), (59, 1), (50608013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
    · exact prime_50608013
  · decide +kernel

theorem prime_3454686179743 : Nat.Prime 3454686179743 := by
  apply nodeValid_prime [2, 3, 7, 82254432851] ⟨3454686179743, 3, [(2, 1), (3, 1), (7, 1), (82254432851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_82254432851
  · decide +kernel

theorem prime_3454686219689 : Nat.Prime 3454686219689 := by
  apply nodeValid_prime [2, 11, 223, 176043937] ⟨3454686219689, 6, [(2, 3), (11, 1), (223, 1), (176043937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_223
    · exact prime_176043937
  · decide +kernel

theorem prime_3454686221513 : Nat.Prime 3454686221513 := by
  apply nodeValid_prime [2, 104161, 4145849] ⟨3454686221513, 3, [(2, 3), (104161, 1), (4145849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_104161
    · exact prime_4145849
  · decide +kernel

theorem prime_3457705253351 : Nat.Prime 3457705253351 := by
  apply nodeValid_prime [2, 5, 317, 218151751] ⟨3457705253351, 13, [(2, 1), (5, 2), (317, 1), (218151751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_317
    · exact prime_218151751
  · decide +kernel

theorem prime_3457705253813 : Nat.Prime 3457705253813 := by
  apply nodeValid_prime [2, 211199, 4092947] ⟨3457705253813, 2, [(2, 2), (211199, 1), (4092947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211199
    · exact prime_4092947
  · decide +kernel

theorem prime_3457705280629 : Nat.Prime 3457705280629 := by
  apply nodeValid_prime [2, 3, 53, 2239, 2428157] ⟨3457705280629, 2, [(2, 2), (3, 1), (53, 1), (2239, 1), (2428157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_2239
    · exact prime_2428157
  · decide +kernel

theorem prime_3460726161131 : Nat.Prime 3460726161131 := by
  apply nodeValid_prime [2, 5, 7, 37, 97, 251, 54881] ⟨3460726161131, 6, [(2, 1), (5, 1), (7, 1), (37, 1), (97, 1), (251, 1), (54881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_97
    · exact prime_251
    · exact prime_54881
  · decide +kernel

theorem prime_3460726214633 : Nat.Prime 3460726214633 := by
  apply nodeValid_prime [2, 37, 315990341] ⟨3460726214633, 3, [(2, 3), (37, 2), (315990341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_315990341
  · decide +kernel

theorem prime_3460726214681 : Nat.Prime 3460726214681 := by
  apply nodeValid_prime [2, 5, 7, 23, 59, 9108133] ⟨3460726214681, 3, [(2, 3), (5, 1), (7, 1), (23, 1), (59, 1), (9108133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_59
    · exact prime_9108133
  · decide +kernel

theorem prime_3463748816383 : Nat.Prime 3463748816383 := by
  apply nodeValid_prime [2, 3, 29, 68767, 96493] ⟨3463748816383, 3, [(2, 1), (3, 2), (29, 1), (68767, 1), (96493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_68767
    · exact prime_96493
  · decide +kernel

theorem prime_3463748839247 : Nat.Prime 3463748839247 := by
  apply nodeValid_prime [2, 41, 1801, 23454103] ⟨3463748839247, 5, [(2, 1), (41, 1), (1801, 1), (23454103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1801
    · exact prime_23454103
  · decide +kernel

theorem prime_3463748839777 : Nat.Prime 3463748839777 := by
  apply nodeValid_prime [2, 3, 36080717081] ⟨3463748839777, 5, [(2, 5), (3, 1), (36080717081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36080717081
  · decide +kernel

theorem prime_3466773236917 : Nat.Prime 3466773236917 := by
  apply nodeValid_prime [2, 3, 11, 83, 105475637] ⟨3466773236917, 2, [(2, 2), (3, 2), (11, 1), (83, 1), (105475637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
    · exact prime_105475637
  · decide +kernel

theorem prime_3466773237101 : Nat.Prime 3466773237101 := by
  apply nodeValid_prime [2, 5, 34667732371] ⟨3466773237101, 2, [(2, 2), (5, 2), (34667732371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_34667732371
  · decide +kernel

theorem prime_3466773256747 : Nat.Prime 3466773256747 := by
  apply nodeValid_prime [2, 3, 3767, 153383473] ⟨3466773256747, 2, [(2, 1), (3, 1), (3767, 1), (153383473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3767
    · exact prime_153383473
  · decide +kernel

theorem prime_3469799490803 : Nat.Prime 3469799490803 := by
  apply nodeValid_prime [2, 43, 73, 552691859] ⟨3469799490803, 2, [(2, 1), (43, 1), (73, 1), (552691859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_73
    · exact prime_552691859
  · decide +kernel

theorem prime_3469799490811 : Nat.Prime 3469799490811 := by
  apply nodeValid_prime [2, 3, 5, 115659983027] ⟨3469799490811, 3, [(2, 1), (3, 1), (5, 1), (115659983027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_115659983027
  · decide +kernel

theorem prime_3469799499247 : Nat.Prime 3469799499247 := by
  apply nodeValid_prime [2, 3, 727, 265153561] ⟨3469799499247, 3, [(2, 1), (3, 2), (727, 1), (265153561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_727
    · exact prime_265153561
  · decide +kernel

theorem prime_3472827511667 : Nat.Prime 3472827511667 := by
  apply nodeValid_prime [2, 37, 125627, 373567] ⟨3472827511667, 2, [(2, 1), (37, 1), (125627, 1), (373567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_125627
    · exact prime_373567
  · decide +kernel

theorem prime_3472827511889 : Nat.Prime 3472827511889 := by
  apply nodeValid_prime [2, 7, 37, 367, 853, 2677] ⟨3472827511889, 3, [(2, 4), (7, 1), (37, 1), (367, 1), (853, 1), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_367
    · exact prime_853
    · exact prime_2677
  · decide +kernel

theorem prime_3472827540121 : Nat.Prime 3472827540121 := by
  apply nodeValid_prime [2, 3, 5, 79, 122110673] ⟨3472827540121, 17, [(2, 3), (3, 2), (5, 1), (79, 1), (122110673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_122110673
  · decide +kernel

theorem prime_3475857279449 : Nat.Prime 3475857279449 := by
  apply nodeValid_prime [2, 4507, 96401633] ⟨3475857279449, 3, [(2, 3), (4507, 1), (96401633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4507
    · exact prime_96401633
  · decide +kernel

theorem prime_3475857279641 : Nat.Prime 3475857279641 := by
  apply nodeValid_prime [2, 5, 17, 11027, 463549] ⟨3475857279641, 3, [(2, 3), (5, 1), (17, 1), (11027, 1), (463549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_11027
    · exact prime_463549
  · decide +kernel

theorem prime_3475857372607 : Nat.Prime 3475857372607 := by
  apply nodeValid_prime [2, 3, 47837, 4036691] ⟨3475857372607, 3, [(2, 1), (3, 2), (47837, 1), (4036691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47837
    · exact prime_4036691
  · decide +kernel

theorem prime_3478888990793 : Nat.Prime 3478888990793 := by
  apply nodeValid_prime [2, 19, 919, 24904709] ⟨3478888990793, 3, [(2, 3), (19, 1), (919, 1), (24904709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_919
    · exact prime_24904709
  · decide +kernel

theorem prime_3478889070967 : Nat.Prime 3478889070967 := by
  apply nodeValid_prime [2, 3, 34513, 16799897] ⟨3478889070967, 6, [(2, 1), (3, 1), (34513, 1), (16799897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34513
    · exact prime_16799897
  · decide +kernel

theorem prime_3478889073047 : Nat.Prime 3478889073047 := by
  apply nodeValid_prime [2, 29, 269, 13417, 16619] ⟨3478889073047, 5, [(2, 1), (29, 1), (269, 1), (13417, 1), (16619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_269
    · exact prime_13417
    · exact prime_16619
  · decide +kernel

theorem prime_3481922405149 : Nat.Prime 3481922405149 := by
  apply nodeValid_prime [2, 3, 11, 26378200039] ⟨3481922405149, 6, [(2, 2), (3, 1), (11, 1), (26378200039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_26378200039
  · decide +kernel

theorem prime_3481922418431 : Nat.Prime 3481922418431 := by
  apply nodeValid_prime [2, 5, 17, 829, 24706751] ⟨3481922418431, 7, [(2, 1), (5, 1), (17, 1), (829, 1), (24706751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_829
    · exact prime_24706751
  · decide +kernel

theorem prime_3481922419771 : Nat.Prime 3481922419771 := by
  apply nodeValid_prime [2, 3, 5, 2579, 45003521] ⟨3481922419771, 11, [(2, 1), (3, 1), (5, 1), (2579, 1), (45003521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2579
    · exact prime_45003521
  · decide +kernel

theorem prime_3484957442627 : Nat.Prime 3484957442627 := by
  apply nodeValid_prime [2, 11, 158407156483] ⟨3484957442627, 2, [(2, 1), (11, 1), (158407156483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_158407156483
  · decide +kernel

theorem prime_3484957442819 : Nat.Prime 3484957442819 := by
  apply nodeValid_prime [2, 43, 59, 686826457] ⟨3484957442819, 2, [(2, 1), (43, 1), (59, 1), (686826457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_59
    · exact prime_686826457
  · decide +kernel

theorem prime_3484957614773 : Nat.Prime 3484957614773 := by
  apply nodeValid_prime [2, 871239403693] ⟨3484957614773, 2, [(2, 2), (871239403693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_871239403693
  · decide +kernel

theorem prime_3487994615393 : Nat.Prime 3487994615393 := by
  apply nodeValid_prime [2, 7, 19, 599, 881, 1553] ⟨3487994615393, 3, [(2, 5), (7, 1), (19, 1), (599, 1), (881, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_599
    · exact prime_881
    · exact prime_1553
  · decide +kernel

theorem prime_3487994622767 : Nat.Prime 3487994622767 := by
  apply nodeValid_prime [2, 557, 1667, 1878257] ⟨3487994622767, 5, [(2, 1), (557, 1), (1667, 1), (1878257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_557
    · exact prime_1667
    · exact prime_1878257
  · decide +kernel

theorem prime_3487994623027 : Nat.Prime 3487994623027 := by
  apply nodeValid_prime [2, 3, 41, 1575426659] ⟨3487994623027, 2, [(2, 1), (3, 3), (41, 1), (1575426659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1575426659
  · decide +kernel

theorem prime_3491033404933 : Nat.Prime 3491033404933 := by
  apply nodeValid_prime [2, 3, 23, 20599, 68227] ⟨3491033404933, 2, [(2, 2), (3, 3), (23, 1), (20599, 1), (68227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_20599
    · exact prime_68227
  · decide +kernel

theorem prime_3491033529593 : Nat.Prime 3491033529593 := by
  apply nodeValid_prime [2, 7, 23, 2710429759] ⟨3491033529593, 3, [(2, 3), (7, 1), (23, 1), (2710429759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_2710429759
  · decide +kernel

theorem prime_3491033530403 : Nat.Prime 3491033530403 := by
  apply nodeValid_prime [2, 11, 158683342291] ⟨3491033530403, 2, [(2, 1), (11, 1), (158683342291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_158683342291
  · decide +kernel

theorem prime_3494073969773 : Nat.Prime 3494073969773 := by
  apply nodeValid_prime [2, 19, 59, 779231483] ⟨3494073969773, 2, [(2, 2), (19, 1), (59, 1), (779231483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59
    · exact prime_779231483
  · decide +kernel

theorem prime_3494073969889 : Nat.Prime 3494073969889 := by
  apply nodeValid_prime [2, 3, 36396603853] ⟨3494073969889, 7, [(2, 5), (3, 1), (36396603853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36396603853
  · decide +kernel

theorem prime_3494073984299 : Nat.Prime 3494073984299 := by
  apply nodeValid_prime [2, 71, 6301, 3905119] ⟨3494073984299, 2, [(2, 1), (71, 1), (6301, 1), (3905119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_6301
    · exact prime_3905119
  · decide +kernel

theorem prime_3497116309441 : Nat.Prime 3497116309441 := by
  apply nodeValid_prime [2, 3, 5, 13, 227, 1234439] ⟨3497116309441, 11, [(2, 6), (3, 1), (5, 1), (13, 1), (227, 1), (1234439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_227
    · exact prime_1234439
  · decide +kernel

theorem prime_3497116309891 : Nat.Prime 3497116309891 := by
  apply nodeValid_prime [2, 3, 5, 7, 2378990687] ⟨3497116309891, 2, [(2, 1), (3, 1), (5, 1), (7, 2), (2378990687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2378990687
  · decide +kernel

theorem prime_3497116353443 : Nat.Prime 3497116353443 := by
  apply nodeValid_prime [2, 107, 51349, 318247] ⟨3497116353443, 2, [(2, 1), (107, 1), (51349, 1), (318247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_51349
    · exact prime_318247
  · decide +kernel

end Sude.Lucas.Generated
