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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0091

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_8263 : Nat.Prime 8263 := by
  apply nodeValid_prime [2, 3, 17] ⟨8263, 3, [(2, 1), (3, 5), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_8581 : Nat.Prime 8581 := by
  apply nodeValid_prime [2, 3, 5, 11, 13] ⟨8581, 6, [(2, 2), (3, 1), (5, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_11717 : Nat.Prime 11717 := by
  apply nodeValid_prime [2, 29, 101] ⟨11717, 2, [(2, 2), (29, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_101
  · decide +kernel

theorem prime_16087 : Nat.Prime 16087 := by
  apply nodeValid_prime [2, 3, 7, 383] ⟨16087, 5, [(2, 1), (3, 1), (7, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
  · decide +kernel

theorem prime_18061 : Nat.Prime 18061 := by
  apply nodeValid_prime [2, 3, 5, 7, 43] ⟨18061, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_23677 : Nat.Prime 23677 := by
  apply nodeValid_prime [2, 3, 1973] ⟨23677, 5, [(2, 2), (3, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1973
  · decide +kernel

theorem prime_23929 : Nat.Prime 23929 := by
  apply nodeValid_prime [2, 3, 997] ⟨23929, 7, [(2, 3), (3, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_997
  · decide +kernel

theorem prime_33053 : Nat.Prime 33053 := by
  apply nodeValid_prime [2, 8263] ⟨33053, 2, [(2, 2), (8263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8263
  · decide +kernel

theorem prime_33461 : Nat.Prime 33461 := by
  apply nodeValid_prime [2, 5, 7, 239] ⟨33461, 3, [(2, 2), (5, 1), (7, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_239
  · decide +kernel

theorem prime_37993 : Nat.Prime 37993 := by
  apply nodeValid_prime [2, 3, 1583] ⟨37993, 10, [(2, 3), (3, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1583
  · decide +kernel

theorem prime_40387 : Nat.Prime 40387 := by
  apply nodeValid_prime [2, 3, 53, 127] ⟨40387, 2, [(2, 1), (3, 1), (53, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_127
  · decide +kernel

theorem prime_43319 : Nat.Prime 43319 := by
  apply nodeValid_prime [2, 11, 179] ⟨43319, 11, [(2, 1), (11, 2), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_179
  · decide +kernel

theorem prime_49121 : Nat.Prime 49121 := by
  apply nodeValid_prime [2, 5, 307] ⟨49121, 3, [(2, 5), (5, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_307
  · decide +kernel

theorem prime_54443 : Nat.Prime 54443 := by
  apply nodeValid_prime [2, 163, 167] ⟨54443, 2, [(2, 1), (163, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_167
  · decide +kernel

theorem prime_61643 : Nat.Prime 61643 := by
  apply nodeValid_prime [2, 7, 17, 37] ⟨61643, 2, [(2, 1), (7, 2), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_61751 : Nat.Prime 61751 := by
  apply nodeValid_prime [2, 5, 13, 19] ⟨61751, 7, [(2, 1), (5, 3), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_63131 : Nat.Prime 63131 := by
  apply nodeValid_prime [2, 5, 59, 107] ⟨63131, 2, [(2, 1), (5, 1), (59, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_107
  · decide +kernel

theorem prime_65963 : Nat.Prime 65963 := by
  apply nodeValid_prime [2, 13, 43, 59] ⟨65963, 2, [(2, 1), (13, 1), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_66499 : Nat.Prime 66499 := by
  apply nodeValid_prime [2, 3, 11083] ⟨66499, 2, [(2, 1), (3, 1), (11083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11083
  · decide +kernel

theorem prime_80051 : Nat.Prime 80051 := by
  apply nodeValid_prime [2, 5, 1601] ⟨80051, 2, [(2, 1), (5, 2), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1601
  · decide +kernel

theorem prime_82007 : Nat.Prime 82007 := by
  apply nodeValid_prime [2, 131, 313] ⟨82007, 5, [(2, 1), (131, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_313
  · decide +kernel

theorem prime_84751 : Nat.Prime 84751 := by
  apply nodeValid_prime [2, 3, 5, 113] ⟨84751, 6, [(2, 1), (3, 1), (5, 3), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_93169 : Nat.Prime 93169 := by
  apply nodeValid_prime [2, 3, 647] ⟨93169, 11, [(2, 4), (3, 2), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_647
  · decide +kernel

theorem prime_94433 : Nat.Prime 94433 := by
  apply nodeValid_prime [2, 13, 227] ⟨94433, 5, [(2, 5), (13, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_227
  · decide +kernel

theorem prime_102653 : Nat.Prime 102653 := by
  apply nodeValid_prime [2, 11, 2333] ⟨102653, 2, [(2, 2), (11, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2333
  · decide +kernel

theorem prime_106501 : Nat.Prime 106501 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨106501, 2, [(2, 2), (3, 1), (5, 3), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_108887 : Nat.Prime 108887 := by
  apply nodeValid_prime [2, 54443] ⟨108887, 5, [(2, 1), (54443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54443
  · decide +kernel

theorem prime_110951 : Nat.Prime 110951 := by
  apply nodeValid_prime [2, 5, 7, 317] ⟨110951, 11, [(2, 1), (5, 2), (7, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_317
  · decide +kernel

theorem prime_123503 : Nat.Prime 123503 := by
  apply nodeValid_prime [2, 61751] ⟨123503, 5, [(2, 1), (61751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61751
  · decide +kernel

theorem prime_123941 : Nat.Prime 123941 := by
  apply nodeValid_prime [2, 5, 6197] ⟨123941, 2, [(2, 2), (5, 1), (6197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6197
  · decide +kernel

theorem prime_136099 : Nat.Prime 136099 := by
  apply nodeValid_prime [2, 3, 7561] ⟨136099, 3, [(2, 1), (3, 2), (7561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7561
  · decide +kernel

theorem prime_146681 : Nat.Prime 146681 := by
  apply nodeValid_prime [2, 5, 19, 193] ⟨146681, 3, [(2, 3), (5, 1), (19, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_193
  · decide +kernel

theorem prime_149257 : Nat.Prime 149257 := by
  apply nodeValid_prime [2, 3, 691] ⟨149257, 5, [(2, 3), (3, 3), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
  · decide +kernel

theorem prime_149909 : Nat.Prime 149909 := by
  apply nodeValid_prime [2, 11, 3407] ⟨149909, 2, [(2, 2), (11, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3407
  · decide +kernel

theorem prime_166457 : Nat.Prime 166457 := by
  apply nodeValid_prime [2, 20807] ⟨166457, 3, [(2, 3), (20807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20807
  · decide +kernel

theorem prime_167711 : Nat.Prime 167711 := by
  apply nodeValid_prime [2, 5, 31, 541] ⟨167711, 11, [(2, 1), (5, 1), (31, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_541
  · decide +kernel

theorem prime_195791 : Nat.Prime 195791 := by
  apply nodeValid_prime [2, 5, 7, 2797] ⟨195791, 7, [(2, 1), (5, 1), (7, 1), (2797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2797
  · decide +kernel

theorem prime_246151 : Nat.Prime 246151 := by
  apply nodeValid_prime [2, 3, 5, 547] ⟨246151, 3, [(2, 1), (3, 2), (5, 2), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_547
  · decide +kernel

theorem prime_270601 : Nat.Prime 270601 := by
  apply nodeValid_prime [2, 3, 5, 11, 41] ⟨270601, 17, [(2, 3), (3, 1), (5, 2), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_279137 : Nat.Prime 279137 := by
  apply nodeValid_prime [2, 11, 13, 61] ⟨279137, 3, [(2, 5), (11, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_279269 : Nat.Prime 279269 := by
  apply nodeValid_prime [2, 11, 577] ⟨279269, 2, [(2, 2), (11, 2), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_577
  · decide +kernel

theorem prime_372677 : Nat.Prime 372677 := by
  apply nodeValid_prime [2, 93169] ⟨372677, 2, [(2, 2), (93169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93169
  · decide +kernel

theorem prime_426691 : Nat.Prime 426691 := by
  apply nodeValid_prime [2, 3, 5, 11, 431] ⟨426691, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_431
  · decide +kernel

theorem prime_450817 : Nat.Prime 450817 := by
  apply nodeValid_prime [2, 3, 587] ⟨450817, 7, [(2, 8), (3, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_587
  · decide +kernel

theorem prime_466321 : Nat.Prime 466321 := by
  apply nodeValid_prime [2, 3, 5, 29, 67] ⟨466321, 13, [(2, 4), (3, 1), (5, 1), (29, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_67
  · decide +kernel

theorem prime_501121 : Nat.Prime 501121 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨501121, 7, [(2, 7), (3, 3), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_524123 : Nat.Prime 524123 := by
  apply nodeValid_prime [2, 71, 3691] ⟨524123, 5, [(2, 1), (71, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_3691
  · decide +kernel

theorem prime_525731 : Nat.Prime 525731 := by
  apply nodeValid_prime [2, 5, 19, 2767] ⟨525731, 10, [(2, 1), (5, 1), (19, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_2767
  · decide +kernel

theorem prime_533543 : Nat.Prime 533543 := by
  apply nodeValid_prime [2, 29, 9199] ⟨533543, 10, [(2, 1), (29, 1), (9199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_9199
  · decide +kernel

theorem prime_639007 : Nat.Prime 639007 := by
  apply nodeValid_prime [2, 3, 106501] ⟨639007, 5, [(2, 1), (3, 1), (106501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_106501
  · decide +kernel

theorem prime_710561 : Nat.Prime 710561 := by
  apply nodeValid_prime [2, 5, 4441] ⟨710561, 3, [(2, 5), (5, 1), (4441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4441
  · decide +kernel

theorem prime_1255357 : Nat.Prime 1255357 := by
  apply nodeValid_prime [2, 3, 34871] ⟨1255357, 2, [(2, 2), (3, 2), (34871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34871
  · decide +kernel

theorem prime_1379897 : Nat.Prime 1379897 := by
  apply nodeValid_prime [2, 7, 41, 601] ⟨1379897, 3, [(2, 3), (7, 1), (41, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_601
  · decide +kernel

theorem prime_1681957 : Nat.Prime 1681957 := by
  apply nodeValid_prime [2, 3, 19, 2459] ⟨1681957, 2, [(2, 2), (3, 2), (19, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2459
  · decide +kernel

theorem prime_1729043 : Nat.Prime 1729043 := by
  apply nodeValid_prime [2, 7, 123503] ⟨1729043, 2, [(2, 1), (7, 1), (123503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_123503
  · decide +kernel

theorem prime_1908311 : Nat.Prime 1908311 := by
  apply nodeValid_prime [2, 5, 23, 8297] ⟨1908311, 13, [(2, 1), (5, 1), (23, 1), (8297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_8297
  · decide +kernel

theorem prime_2030317 : Nat.Prime 2030317 := by
  apply nodeValid_prime [2, 3, 71, 2383] ⟨2030317, 2, [(2, 2), (3, 1), (71, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_2383
  · decide +kernel

theorem prime_3458087 : Nat.Prime 3458087 := by
  apply nodeValid_prime [2, 1729043] ⟨3458087, 5, [(2, 1), (1729043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1729043
  · decide +kernel

theorem prime_3613789 : Nat.Prime 3613789 := by
  apply nodeValid_prime [2, 3, 33461] ⟨3613789, 10, [(2, 2), (3, 3), (33461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33461
  · decide +kernel

theorem prime_4890019 : Nat.Prime 4890019 := by
  apply nodeValid_prime [2, 3, 7, 173, 673] ⟨4890019, 2, [(2, 1), (3, 1), (7, 1), (173, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173
    · exact prime_673
  · decide +kernel

theorem prime_5214283 : Nat.Prime 5214283 := by
  apply nodeValid_prime [2, 3, 379, 2293] ⟨5214283, 3, [(2, 1), (3, 1), (379, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_2293
  · decide +kernel

theorem prime_5332123 : Nat.Prime 5332123 := by
  apply nodeValid_prime [2, 3, 19, 5197] ⟨5332123, 3, [(2, 1), (3, 3), (19, 1), (5197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_5197
  · decide +kernel

theorem prime_5700157 : Nat.Prime 5700157 := by
  apply nodeValid_prime [2, 3, 7, 11, 31, 199] ⟨5700157, 6, [(2, 2), (3, 1), (7, 1), (11, 1), (31, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_199
  · decide +kernel

theorem prime_6289477 : Nat.Prime 6289477 := by
  apply nodeValid_prime [2, 3, 524123] ⟨6289477, 5, [(2, 2), (3, 1), (524123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_524123
  · decide +kernel

theorem prime_6827057 : Nat.Prime 6827057 := by
  apply nodeValid_prime [2, 426691] ⟨6827057, 3, [(2, 4), (426691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_426691
  · decide +kernel

theorem prime_8526733 : Nat.Prime 8526733 := by
  apply nodeValid_prime [2, 3, 710561] ⟨8526733, 2, [(2, 2), (3, 1), (710561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_710561
  · decide +kernel

theorem prime_12163181 : Nat.Prime 12163181 := by
  apply nodeValid_prime [2, 5, 29, 67, 313] ⟨12163181, 11, [(2, 2), (5, 1), (29, 1), (67, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_67
    · exact prime_313
  · decide +kernel

theorem prime_12418331 : Nat.Prime 12418331 := by
  apply nodeValid_prime [2, 5, 17, 4297] ⟨12418331, 2, [(2, 1), (5, 1), (17, 2), (4297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_4297
  · decide +kernel

theorem prime_12805033 : Nat.Prime 12805033 := by
  apply nodeValid_prime [2, 3, 533543] ⟨12805033, 5, [(2, 3), (3, 1), (533543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_533543
  · decide +kernel

theorem prime_13598353 : Nat.Prime 13598353 := by
  apply nodeValid_prime [2, 3, 94433] ⟨13598353, 7, [(2, 4), (3, 2), (94433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_94433
  · decide +kernel

theorem prime_14161727 : Nat.Prime 14161727 := by
  apply nodeValid_prime [2, 19, 372677] ⟨14161727, 5, [(2, 1), (19, 1), (372677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_372677
  · decide +kernel

theorem prime_19984319 : Nat.Prime 19984319 := by
  apply nodeValid_prime [2, 263, 37993] ⟨19984319, 11, [(2, 1), (263, 1), (37993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_37993
  · decide +kernel

theorem prime_20816791 : Nat.Prime 20816791 := by
  apply nodeValid_prime [2, 3, 5, 149, 4657] ⟨20816791, 6, [(2, 1), (3, 1), (5, 1), (149, 1), (4657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
    · exact prime_4657
  · decide +kernel

theorem prime_20833931 : Nat.Prime 20833931 := by
  apply nodeValid_prime [2, 5, 13, 43, 3727] ⟨20833931, 2, [(2, 1), (5, 1), (13, 1), (43, 1), (3727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_3727
  · decide +kernel

theorem prime_21365737 : Nat.Prime 21365737 := by
  apply nodeValid_prime [2, 3, 7, 17, 7481] ⟨21365737, 5, [(2, 3), (3, 1), (7, 1), (17, 1), (7481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_7481
  · decide +kernel

theorem prime_24326363 : Nat.Prime 24326363 := by
  apply nodeValid_prime [2, 12163181] ⟨24326363, 2, [(2, 1), (12163181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12163181
  · decide +kernel

theorem prime_31992739 : Nat.Prime 31992739 := by
  apply nodeValid_prime [2, 3, 5332123] ⟨31992739, 2, [(2, 1), (3, 1), (5332123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5332123
  · decide +kernel

theorem prime_32802823 : Nat.Prime 32802823 := by
  apply nodeValid_prime [2, 3, 13, 103, 1361] ⟨32802823, 3, [(2, 1), (3, 2), (13, 1), (103, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
    · exact prime_1361
  · decide +kernel

theorem prime_38137951 : Nat.Prime 38137951 := by
  apply nodeValid_prime [2, 3, 5, 84751] ⟨38137951, 3, [(2, 1), (3, 2), (5, 2), (84751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_84751
  · decide +kernel

theorem prime_39968639 : Nat.Prime 39968639 := by
  apply nodeValid_prime [2, 19984319] ⟨39968639, 7, [(2, 1), (19984319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19984319
  · decide +kernel

theorem prime_49994687 : Nat.Prime 49994687 := by
  apply nodeValid_prime [2, 7, 23, 139, 1117] ⟨49994687, 5, [(2, 1), (7, 1), (23, 1), (139, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_139
    · exact prime_1117
  · decide +kernel

theorem prime_55854017 : Nat.Prime 55854017 := by
  apply nodeValid_prime [2, 37, 103, 229] ⟨55854017, 3, [(2, 6), (37, 1), (103, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_103
    · exact prime_229
  · decide +kernel

theorem prime_56470873 : Nat.Prime 56470873 := by
  apply nodeValid_prime [2, 3, 17, 61, 2269] ⟨56470873, 10, [(2, 3), (3, 1), (17, 1), (61, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_61
    · exact prime_2269
  · decide +kernel

theorem prime_58376029 : Nat.Prime 58376029 := by
  apply nodeValid_prime [2, 3, 17, 67, 4271] ⟨58376029, 7, [(2, 2), (3, 1), (17, 1), (67, 1), (4271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
    · exact prime_4271
  · decide +kernel

theorem prime_68152457 : Nat.Prime 68152457 := by
  apply nodeValid_prime [2, 17, 501121] ⟨68152457, 3, [(2, 3), (17, 1), (501121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_501121
  · decide +kernel

theorem prime_113710609 : Nat.Prime 113710609 := by
  apply nodeValid_prime [2, 3, 11, 23929] ⟨113710609, 7, [(2, 4), (3, 3), (11, 1), (23929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23929
  · decide +kernel

theorem prime_134004067 : Nat.Prime 134004067 := by
  apply nodeValid_prime [2, 3, 7, 79, 40387] ⟨134004067, 2, [(2, 1), (3, 1), (7, 1), (79, 1), (40387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_40387
  · decide +kernel

theorem prime_168116023 : Nat.Prime 168116023 := by
  apply nodeValid_prime [2, 3, 1543, 6053] ⟨168116023, 5, [(2, 1), (3, 2), (1543, 1), (6053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1543
    · exact prime_6053
  · decide +kernel

theorem prime_183648253 : Nat.Prime 183648253 := by
  apply nodeValid_prime [2, 3, 937, 16333] ⟨183648253, 2, [(2, 2), (3, 1), (937, 1), (16333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_937
    · exact prime_16333
  · decide +kernel

theorem prime_193398253 : Nat.Prime 193398253 := by
  apply nodeValid_prime [2, 3, 157, 102653] ⟨193398253, 2, [(2, 2), (3, 1), (157, 1), (102653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_102653
  · decide +kernel

theorem prime_292557679 : Nat.Prime 292557679 := by
  apply nodeValid_prime [2, 3, 7, 113, 61643] ⟨292557679, 3, [(2, 1), (3, 1), (7, 1), (113, 1), (61643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
    · exact prime_61643
  · decide +kernel

theorem prime_309526279 : Nat.Prime 309526279 := by
  apply nodeValid_prime [2, 3, 73, 263, 2687] ⟨309526279, 3, [(2, 1), (3, 1), (73, 1), (263, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_263
    · exact prime_2687
  · decide +kernel

theorem prime_376069751 : Nat.Prime 376069751 := by
  apply nodeValid_prime [2, 5, 7, 17, 12641] ⟨376069751, 21, [(2, 1), (5, 3), (7, 1), (17, 1), (12641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_12641
  · decide +kernel

theorem prime_384583267 : Nat.Prime 384583267 := by
  apply nodeValid_prime [2, 3, 21365737] ⟨384583267, 3, [(2, 1), (3, 2), (21365737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21365737
  · decide +kernel

theorem prime_684138271 : Nat.Prime 684138271 := by
  apply nodeValid_prime [2, 3, 5, 137, 166457] ⟨684138271, 12, [(2, 1), (3, 1), (5, 1), (137, 1), (166457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_166457
  · decide +kernel

theorem prime_725498203 : Nat.Prime 725498203 := by
  apply nodeValid_prime [2, 3, 11, 13, 757, 1117] ⟨725498203, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (757, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_757
    · exact prime_1117
  · decide +kernel

theorem prime_773593013 : Nat.Prime 773593013 := by
  apply nodeValid_prime [2, 193398253] ⟨773593013, 2, [(2, 2), (193398253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193398253
  · decide +kernel

theorem prime_894119833 : Nat.Prime 894119833 := by
  apply nodeValid_prime [2, 3, 12418331] ⟨894119833, 5, [(2, 3), (3, 2), (12418331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12418331
  · decide +kernel

theorem prime_2022068429 : Nat.Prime 2022068429 := by
  apply nodeValid_prime [2, 1811, 279137] ⟨2022068429, 2, [(2, 2), (1811, 1), (279137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1811
    · exact prime_279137
  · decide +kernel

theorem prime_2792700851 : Nat.Prime 2792700851 := by
  apply nodeValid_prime [2, 5, 55854017] ⟨2792700851, 2, [(2, 1), (5, 2), (55854017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_55854017
  · decide +kernel

theorem prime_4104829627 : Nat.Prime 4104829627 := by
  apply nodeValid_prime [2, 3, 684138271] ⟨4104829627, 3, [(2, 1), (3, 1), (684138271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_684138271
  · decide +kernel

theorem prime_4226838487 : Nat.Prime 4226838487 := by
  apply nodeValid_prime [2, 3, 13, 17, 37, 101, 853] ⟨4226838487, 3, [(2, 1), (3, 1), (13, 1), (17, 1), (37, 1), (101, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_37
    · exact prime_101
    · exact prime_853
  · decide +kernel

theorem prime_5364718999 : Nat.Prime 5364718999 := by
  apply nodeValid_prime [2, 3, 894119833] ⟨5364718999, 3, [(2, 1), (3, 1), (894119833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_894119833
  · decide +kernel

theorem prime_6890626607 : Nat.Prime 6890626607 := by
  apply nodeValid_prime [2, 29, 733, 162079] ⟨6890626607, 5, [(2, 1), (29, 1), (733, 1), (162079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_733
    · exact prime_162079
  · decide +kernel

theorem prime_14468038943 : Nat.Prime 14468038943 := by
  apply nodeValid_prime [2, 7, 509, 2030317] ⟨14468038943, 5, [(2, 1), (7, 1), (509, 1), (2030317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_509
    · exact prime_2030317
  · decide +kernel

theorem prime_14871809929 : Nat.Prime 14871809929 := by
  apply nodeValid_prime [2, 3, 29, 157, 136099] ⟨14871809929, 13, [(2, 3), (3, 1), (29, 1), (157, 1), (136099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_157
    · exact prime_136099
  · decide +kernel

theorem prime_16907353949 : Nat.Prime 16907353949 := by
  apply nodeValid_prime [2, 4226838487] ⟨16907353949, 2, [(2, 2), (4226838487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4226838487
  · decide +kernel

theorem prime_16971117929 : Nat.Prime 16971117929 := by
  apply nodeValid_prime [2, 61, 233, 149257] ⟨16971117929, 3, [(2, 3), (61, 1), (233, 1), (149257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_233
    · exact prime_149257
  · decide +kernel

theorem prime_81395917399 : Nat.Prime 81395917399 := by
  apply nodeValid_prime [2, 3, 41, 2347, 46993] ⟨81395917399, 3, [(2, 1), (3, 2), (41, 1), (2347, 1), (46993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2347
    · exact prime_46993
  · decide +kernel

theorem prime_195826521857 : Nat.Prime 195826521857 := by
  apply nodeValid_prime [2, 7, 17, 31, 6689] ⟨195826521857, 3, [(2, 8), (7, 1), (17, 1), (31, 2), (6689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_6689
  · decide +kernel

theorem prime_197675799239 : Nat.Prime 197675799239 := by
  apply nodeValid_prime [2, 257, 384583267] ⟨197675799239, 7, [(2, 1), (257, 1), (384583267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_384583267
  · decide +kernel

theorem prime_277005932971 : Nat.Prime 277005932971 := by
  apply nodeValid_prime [2, 3, 5, 13, 19, 67, 103, 5417] ⟨277005932971, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (67, 1), (103, 1), (5417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_67
    · exact prime_103
    · exact prime_5417
  · decide +kernel

theorem prime_343342015937 : Nat.Prime 343342015937 := by
  apply nodeValid_prime [2, 5364718999] ⟨343342015937, 3, [(2, 6), (5364718999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5364718999
  · decide +kernel

theorem prime_1390234067861 : Nat.Prime 1390234067861 := by
  apply nodeValid_prime [2, 5, 11, 17, 8581, 43319] ⟨1390234067861, 2, [(2, 2), (5, 1), (11, 1), (17, 1), (8581, 1), (43319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_8581
    · exact prime_43319
  · decide +kernel

theorem prime_2728688073367 : Nat.Prime 2728688073367 := by
  apply nodeValid_prime [2, 3, 6673, 68152457] ⟨2728688073367, 3, [(2, 1), (3, 1), (6673, 1), (68152457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6673
    · exact prime_68152457
  · decide +kernel

theorem prime_2728688136373 : Nat.Prime 2728688136373 := by
  apply nodeValid_prime [2, 3, 11, 6890626607] ⟨2728688136373, 2, [(2, 2), (3, 2), (11, 1), (6890626607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6890626607
  · decide +kernel

theorem prime_2728688137711 : Nat.Prime 2728688137711 := by
  apply nodeValid_prime [2, 3, 5, 3739, 24326363] ⟨2728688137711, 15, [(2, 1), (3, 1), (5, 1), (3739, 1), (24326363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3739
    · exact prime_24326363
  · decide +kernel

theorem prime_2731261424783 : Nat.Prime 2731261424783 := by
  apply nodeValid_prime [2, 11, 83, 271, 66499] ⟨2731261424783, 5, [(2, 1), (11, 1), (83, 2), (271, 1), (66499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83
    · exact prime_271
    · exact prime_66499
  · decide +kernel

theorem prime_2731261432223 : Nat.Prime 2731261432223 := by
  apply nodeValid_prime [2, 279269, 4890019] ⟨2731261432223, 5, [(2, 1), (279269, 1), (4890019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_279269
    · exact prime_4890019
  · decide +kernel

theorem prime_2731261432279 : Nat.Prime 2731261432279 := by
  apply nodeValid_prime [2, 3, 163, 2792700851] ⟨2731261432279, 6, [(2, 1), (3, 1), (163, 1), (2792700851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_2792700851
  · decide +kernel

theorem prime_2733836426989 : Nat.Prime 2733836426989 := by
  apply nodeValid_prime [2, 3, 16087, 14161727] ⟨2733836426989, 2, [(2, 2), (3, 1), (16087, 1), (14161727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16087
    · exact prime_14161727
  · decide +kernel

theorem prime_2733836516009 : Nat.Prime 2733836516009 := by
  apply nodeValid_prime [2, 13, 2022068429] ⟨2733836516009, 3, [(2, 3), (13, 2), (2022068429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2022068429
  · decide +kernel

theorem prime_2736413025233 : Nat.Prime 2736413025233 := by
  apply nodeValid_prime [2, 123941, 1379897] ⟨2736413025233, 3, [(2, 4), (123941, 1), (1379897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_123941
    · exact prime_1379897
  · decide +kernel

theorem prime_2736413026937 : Nat.Prime 2736413026937 := by
  apply nodeValid_prime [2, 23, 14871809929] ⟨2736413026937, 3, [(2, 3), (23, 1), (14871809929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_14871809929
  · decide +kernel

theorem prime_2736413074207 : Nat.Prime 2736413074207 := by
  apply nodeValid_prime [2, 3, 7, 1151, 6289477] ⟨2736413074207, 3, [(2, 1), (3, 3), (7, 1), (1151, 1), (6289477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1151
    · exact prime_6289477
  · decide +kernel

theorem prime_2738991338779 : Nat.Prime 2738991338779 := by
  apply nodeValid_prime [2, 3, 281, 25733, 63131] ⟨2738991338779, 3, [(2, 1), (3, 1), (281, 1), (25733, 1), (63131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_25733
    · exact prime_63131
  · decide +kernel

theorem prime_2738991339739 : Nat.Prime 2738991339739 := by
  apply nodeValid_prime [2, 3, 16907353949] ⟨2738991339739, 2, [(2, 1), (3, 4), (16907353949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16907353949
  · decide +kernel

theorem prime_2738991364919 : Nat.Prime 2738991364919 := by
  apply nodeValid_prime [2, 149, 241, 38137951] ⟨2738991364919, 19, [(2, 1), (149, 1), (241, 1), (38137951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_241
    · exact prime_38137951
  · decide +kernel

theorem prime_2741571305999 : Nat.Prime 2741571305999 := by
  apply nodeValid_prime [2, 7, 195826521857] ⟨2741571305999, 7, [(2, 1), (7, 1), (195826521857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_195826521857
  · decide +kernel

theorem prime_2741571373601 : Nat.Prime 2741571373601 := by
  apply nodeValid_prime [2, 5, 991, 3458087] ⟨2741571373601, 3, [(2, 5), (5, 2), (991, 1), (3458087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_991
    · exact prime_3458087
  · decide +kernel

theorem prime_2741571374701 : Nat.Prime 2741571374701 := by
  apply nodeValid_prime [2, 3, 5, 439, 20816791] ⟨2741571374701, 2, [(2, 2), (3, 1), (5, 2), (439, 1), (20816791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_439
    · exact prime_20816791
  · decide +kernel

theorem prime_2744152894079 : Nat.Prime 2744152894079 := by
  apply nodeValid_prime [2, 157, 727, 2063, 5827] ⟨2744152894079, 7, [(2, 1), (157, 1), (727, 1), (2063, 1), (5827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_727
    · exact prime_2063
    · exact prime_5827
  · decide +kernel

theorem prime_2744152960889 : Nat.Prime 2744152960889 := by
  apply nodeValid_prime [2, 10457, 32802823] ⟨2744152960889, 3, [(2, 3), (10457, 1), (32802823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10457
    · exact prime_32802823
  · decide +kernel

theorem prime_2746736127497 : Nat.Prime 2746736127497 := by
  apply nodeValid_prime [2, 343342015937] ⟨2746736127497, 3, [(2, 3), (343342015937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_343342015937
  · decide +kernel

theorem prime_2746736196559 : Nat.Prime 2746736196559 := by
  apply nodeValid_prime [2, 3, 631, 725498203] ⟨2746736196559, 3, [(2, 1), (3, 1), (631, 1), (725498203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
    · exact prime_725498203
  · decide +kernel

theorem prime_2746736199847 : Nat.Prime 2746736199847 := by
  apply nodeValid_prime [2, 3, 17, 29, 309526279] ⟨2746736199847, 3, [(2, 1), (3, 2), (17, 1), (29, 1), (309526279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_309526279
  · decide +kernel

theorem prime_2749320999011 : Nat.Prime 2749320999011 := by
  apply nodeValid_prime [2, 5, 179, 3407, 450817] ⟨2749320999011, 2, [(2, 1), (5, 1), (179, 1), (3407, 1), (450817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_3407
    · exact prime_450817
  · decide +kernel

theorem prime_2749321104499 : Nat.Prime 2749321104499 := by
  apply nodeValid_prime [2, 3, 16971117929] ⟨2749321104499, 2, [(2, 1), (3, 4), (16971117929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16971117929
  · decide +kernel

theorem prime_2751907519913 : Nat.Prime 2751907519913 := by
  apply nodeValid_prime [2, 17, 151, 134004067] ⟨2751907519913, 3, [(2, 3), (17, 1), (151, 1), (134004067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_151
    · exact prime_134004067
  · decide +kernel

theorem prime_2751907551079 : Nat.Prime 2751907551079 := by
  apply nodeValid_prime [2, 3, 7, 18131, 3613789] ⟨2751907551079, 3, [(2, 1), (3, 1), (7, 1), (18131, 1), (3613789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18131
    · exact prime_3613789
  · decide +kernel

theorem prime_2751907551229 : Nat.Prime 2751907551229 := by
  apply nodeValid_prime [2, 3, 11, 139, 49994687] ⟨2751907551229, 10, [(2, 2), (3, 2), (11, 1), (139, 1), (49994687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
    · exact prime_49994687
  · decide +kernel

theorem prime_2754495685373 : Nat.Prime 2754495685373 := by
  apply nodeValid_prime [2, 33053, 20833931] ⟨2754495685373, 2, [(2, 2), (33053, 1), (20833931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_33053
    · exact prime_20833931
  · decide +kernel

theorem prime_2754495709369 : Nat.Prime 2754495709369 := by
  apply nodeValid_prime [2, 3, 13, 23, 6029, 63667] ⟨2754495709369, 7, [(2, 3), (3, 1), (13, 1), (23, 1), (6029, 1), (63667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_6029
    · exact prime_63667
  · decide +kernel

theorem prime_2754495710437 : Nat.Prime 2754495710437 := by
  apply nodeValid_prime [2, 3, 19, 108887, 110951] ⟨2754495710437, 2, [(2, 2), (3, 1), (19, 1), (108887, 1), (110951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_108887
    · exact prime_110951
  · decide +kernel

theorem prime_2757085494209 : Nat.Prime 2757085494209 := by
  apply nodeValid_prime [2, 509, 1723, 49121] ⟨2757085494209, 3, [(2, 6), (509, 1), (1723, 1), (49121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_1723
    · exact prime_49121
  · decide +kernel

theorem prime_2757085495001 : Nat.Prime 2757085495001 := by
  apply nodeValid_prime [2, 5, 11527, 47837] ⟨2757085495001, 3, [(2, 3), (5, 4), (11527, 1), (47837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11527
    · exact prime_47837
  · decide +kernel

theorem prime_2757085498333 : Nat.Prime 2757085498333 := by
  apply nodeValid_prime [2, 3, 11, 773593013] ⟨2757085498333, 6, [(2, 2), (3, 4), (11, 1), (773593013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_773593013
  · decide +kernel

theorem prime_2759676879727 : Nat.Prime 2759676879727 := by
  apply nodeValid_prime [2, 3, 13, 151, 521, 149909] ⟨2759676879727, 5, [(2, 1), (3, 2), (13, 1), (151, 1), (521, 1), (149909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_151
    · exact prime_521
    · exact prime_149909
  · decide +kernel

theorem prime_2759676880621 : Nat.Prime 2759676880621 := by
  apply nodeValid_prime [2, 3, 5, 11, 63389, 65963] ⟨2759676880621, 17, [(2, 2), (3, 1), (5, 1), (11, 1), (63389, 1), (65963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_63389
    · exact prime_65963
  · decide +kernel

theorem prime_2759676954527 : Nat.Prime 2759676954527 := by
  apply nodeValid_prime [2, 29, 3499, 13598353] ⟨2759676954527, 5, [(2, 1), (29, 1), (3499, 1), (13598353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3499
    · exact prime_13598353
  · decide +kernel

theorem prime_2762269991311 : Nat.Prime 2762269991311 := by
  apply nodeValid_prime [2, 3, 5, 2087, 2927, 15073] ⟨2762269991311, 3, [(2, 1), (3, 1), (5, 1), (2087, 1), (2927, 1), (15073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2087
    · exact prime_2927
    · exact prime_15073
  · decide +kernel

theorem prime_2762269991729 : Nat.Prime 2762269991729 := by
  apply nodeValid_prime [2, 13, 97, 233, 251, 2341] ⟨2762269991729, 3, [(2, 4), (13, 1), (97, 1), (233, 1), (251, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_97
    · exact prime_233
    · exact prime_251
    · exact prime_2341
  · decide +kernel

theorem prime_2762270065279 : Nat.Prime 2762270065279 := by
  apply nodeValid_prime [2, 3, 80051, 639007] ⟨2762270065279, 3, [(2, 1), (3, 3), (80051, 1), (639007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80051
    · exact prime_639007
  · decide +kernel

theorem prime_2764864809353 : Nat.Prime 2764864809353 := by
  apply nodeValid_prime [2, 919, 376069751] ⟨2764864809353, 3, [(2, 3), (919, 1), (376069751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_919
    · exact prime_376069751
  · decide +kernel

theorem prime_2764864830967 : Nat.Prime 2764864830967 := by
  apply nodeValid_prime [2, 3, 7, 39139, 1681957] ⟨2764864830967, 3, [(2, 1), (3, 1), (7, 1), (39139, 1), (1681957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_39139
    · exact prime_1681957
  · decide +kernel

theorem prime_2767461189347 : Nat.Prime 2767461189347 := by
  apply nodeValid_prime [2, 7, 197675799239] ⟨2767461189347, 2, [(2, 1), (7, 1), (197675799239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_197675799239
  · decide +kernel

theorem prime_2767461191567 : Nat.Prime 2767461191567 := by
  apply nodeValid_prime [2, 17, 81395917399] ⟨2767461191567, 5, [(2, 1), (17, 1), (81395917399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_81395917399
  · decide +kernel

theorem prime_2767461249071 : Nat.Prime 2767461249071 := by
  apply nodeValid_prime [2, 5, 7, 149, 569, 466321] ⟨2767461249071, 7, [(2, 1), (5, 1), (7, 1), (149, 1), (569, 1), (466321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_149
    · exact prime_569
    · exact prime_466321
  · decide +kernel

theorem prime_2770059313577 : Nat.Prime 2770059313577 := by
  apply nodeValid_prime [2, 79, 137, 31992739] ⟨2770059313577, 3, [(2, 3), (79, 1), (137, 1), (31992739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_137
    · exact prime_31992739
  · decide +kernel

theorem prime_2770059328109 : Nat.Prime 2770059328109 := by
  apply nodeValid_prime [2, 11863, 58376029] ⟨2770059328109, 2, [(2, 2), (11863, 1), (58376029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11863
    · exact prime_58376029
  · decide +kernel

theorem prime_2770059329711 : Nat.Prime 2770059329711 := by
  apply nodeValid_prime [2, 5, 277005932971] ⟨2770059329711, 7, [(2, 1), (5, 1), (277005932971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_277005932971
  · decide +kernel

theorem prime_2772659004121 : Nat.Prime 2772659004121 := by
  apply nodeValid_prime [2, 3, 5, 139, 283, 195791] ⟨2772659004121, 13, [(2, 3), (3, 2), (5, 1), (139, 1), (283, 1), (195791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_283
    · exact prime_195791
  · decide +kernel

theorem prime_2772659005297 : Nat.Prime 2772659005297 := by
  apply nodeValid_prime [2, 3, 8461, 6827057] ⟨2772659005297, 5, [(2, 4), (3, 1), (8461, 1), (6827057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8461
    · exact prime_6827057
  · decide +kernel

theorem prime_2772659026301 : Nat.Prime 2772659026301 := by
  apply nodeValid_prime [2, 5, 79, 1297, 270601] ⟨2772659026301, 3, [(2, 2), (5, 2), (79, 1), (1297, 1), (270601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_1297
    · exact prime_270601
  · decide +kernel

theorem prime_2775260402039 : Nat.Prime 2775260402039 := by
  apply nodeValid_prime [2, 31, 181, 197, 1255357] ⟨2775260402039, 11, [(2, 1), (31, 1), (181, 1), (197, 1), (1255357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_181
    · exact prime_197
    · exact prime_1255357
  · decide +kernel

theorem prime_2775260412157 : Nat.Prime 2775260412157 := by
  apply nodeValid_prime [2, 3, 18061, 12805033] ⟨2775260412157, 5, [(2, 2), (3, 1), (18061, 1), (12805033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18061
    · exact prime_12805033
  · decide +kernel

theorem prime_2775260412487 : Nat.Prime 2775260412487 := by
  apply nodeValid_prime [2, 3, 29569, 5214283] ⟨2775260412487, 5, [(2, 1), (3, 2), (29569, 1), (5214283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29569
    · exact prime_5214283
  · decide +kernel

theorem prime_2777863440127 : Nat.Prime 2777863440127 := by
  apply nodeValid_prime [2, 3, 19, 113, 1908311] ⟨2777863440127, 3, [(2, 1), (3, 1), (19, 1), (113, 2), (1908311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_113
    · exact prime_1908311
  · decide +kernel

theorem prime_2777863474879 : Nat.Prime 2777863474879 := by
  apply nodeValid_prime [2, 3, 2521, 183648253] ⟨2777863474879, 3, [(2, 1), (3, 1), (2521, 1), (183648253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2521
    · exact prime_183648253
  · decide +kernel

theorem prime_2777863477057 : Nat.Prime 2777863477057 := by
  apply nodeValid_prime [2, 3, 14468038943] ⟨2777863477057, 13, [(2, 6), (3, 1), (14468038943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14468038943
  · decide +kernel

theorem prime_2780468135723 : Nat.Prime 2780468135723 := by
  apply nodeValid_prime [2, 1390234067861] ⟨2780468135723, 2, [(2, 1), (1390234067861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1390234067861
  · decide +kernel

theorem prime_2780468181217 : Nat.Prime 2780468181217 := by
  apply nodeValid_prime [2, 3, 11, 292557679] ⟨2780468181217, 15, [(2, 5), (3, 3), (11, 1), (292557679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_292557679
  · decide +kernel

theorem prime_2780468182717 : Nat.Prime 2780468182717 := by
  apply nodeValid_prime [2, 3, 7, 5807, 5700157] ⟨2780468182717, 2, [(2, 2), (3, 1), (7, 1), (5807, 1), (5700157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5807
    · exact prime_5700157
  · decide +kernel

theorem prime_2783074487107 : Nat.Prime 2783074487107 := by
  apply nodeValid_prime [2, 3, 113, 4104829627] ⟨2783074487107, 2, [(2, 1), (3, 1), (113, 1), (4104829627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_4104829627
  · decide +kernel

theorem prime_2783074487327 : Nat.Prime 2783074487327 := by
  apply nodeValid_prime [2, 7, 167711, 1185319] ⟨2783074487327, 5, [(2, 1), (7, 1), (167711, 1), (1185319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_167711
    · exact prime_1185319
  · decide +kernel

theorem prime_2783074490803 : Nat.Prime 2783074490803 := by
  apply nodeValid_prime [2, 3, 18133, 8526733] ⟨2783074490803, 3, [(2, 1), (3, 2), (18133, 1), (8526733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18133
    · exact prime_8526733
  · decide +kernel

theorem prime_2785682497867 : Nat.Prime 2785682497867 := by
  apply nodeValid_prime [2, 3, 23, 82007, 246151] ⟨2785682497867, 2, [(2, 1), (3, 1), (23, 1), (82007, 1), (246151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_82007
    · exact prime_246151
  · decide +kernel

theorem prime_2785682499283 : Nat.Prime 2785682499283 := by
  apply nodeValid_prime [2, 3, 1361, 113710609] ⟨2785682499283, 2, [(2, 1), (3, 2), (1361, 1), (113710609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1361
    · exact prime_113710609
  · decide +kernel

theorem prime_2785682501111 : Nat.Prime 2785682501111 := by
  apply nodeValid_prime [2, 5, 1657, 168116023] ⟨2785682501111, 22, [(2, 1), (5, 1), (1657, 1), (168116023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1657
    · exact prime_168116023
  · decide +kernel

theorem prime_2788292166689 : Nat.Prime 2788292166689 := by
  apply nodeValid_prime [2, 7, 23677, 525731] ⟨2788292166689, 3, [(2, 5), (7, 1), (23677, 1), (525731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23677
    · exact prime_525731
  · decide +kernel

theorem prime_2788292193469 : Nat.Prime 2788292193469 := by
  apply nodeValid_prime [2, 3, 79, 173, 1451, 11717] ⟨2788292193469, 2, [(2, 2), (3, 1), (79, 1), (173, 1), (1451, 1), (11717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_173
    · exact prime_1451
    · exact prime_11717
  · decide +kernel

theorem prime_2788292193919 : Nat.Prime 2788292193919 := by
  apply nodeValid_prime [2, 3, 7, 11, 151, 39968639] ⟨2788292193919, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (151, 1), (39968639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_151
    · exact prime_39968639
  · decide +kernel

theorem prime_2790903485407 : Nat.Prime 2790903485407 := by
  apply nodeValid_prime [2, 3, 8237, 56470873] ⟨2790903485407, 5, [(2, 1), (3, 1), (8237, 1), (56470873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8237
    · exact prime_56470873
  · decide +kernel

theorem prime_2790903494069 : Nat.Prime 2790903494069 := by
  apply nodeValid_prime [2, 37, 59, 2179, 146681] ⟨2790903494069, 2, [(2, 2), (37, 1), (59, 1), (2179, 1), (146681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_59
    · exact prime_2179
    · exact prime_146681
  · decide +kernel

end Sude.Lucas.Generated
