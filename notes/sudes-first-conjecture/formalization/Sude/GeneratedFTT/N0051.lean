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
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0049

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3041 : Nat.Prime 3041 := by
  apply nodeValid_prime [2, 5, 19] ⟨3041, 3, [(2, 5), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_3373 : Nat.Prime 3373 := by
  apply nodeValid_prime [2, 3, 281] ⟨3373, 5, [(2, 2), (3, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
  · decide +kernel

theorem prime_3449 : Nat.Prime 3449 := by
  apply nodeValid_prime [2, 431] ⟨3449, 3, [(2, 3), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_431
  · decide +kernel

theorem prime_4027 : Nat.Prime 4027 := by
  apply nodeValid_prime [2, 3, 11, 61] ⟨4027, 3, [(2, 1), (3, 1), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_4691 : Nat.Prime 4691 := by
  apply nodeValid_prime [2, 5, 7, 67] ⟨4691, 2, [(2, 1), (5, 1), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_5563 : Nat.Prime 5563 := by
  apply nodeValid_prime [2, 3, 103] ⟨5563, 2, [(2, 1), (3, 3), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_6473 : Nat.Prime 6473 := by
  apply nodeValid_prime [2, 809] ⟨6473, 3, [(2, 3), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_809
  · decide +kernel

theorem prime_6899 : Nat.Prime 6899 := by
  apply nodeValid_prime [2, 3449] ⟨6899, 2, [(2, 1), (3449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3449
  · decide +kernel

theorem prime_7477 : Nat.Prime 7477 := by
  apply nodeValid_prime [2, 3, 7, 89] ⟨7477, 2, [(2, 2), (3, 1), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_8429 : Nat.Prime 8429 := by
  apply nodeValid_prime [2, 7, 43] ⟨8429, 2, [(2, 2), (7, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_8971 : Nat.Prime 8971 := by
  apply nodeValid_prime [2, 3, 5, 13, 23] ⟨8971, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_9769 : Nat.Prime 9769 := by
  apply nodeValid_prime [2, 3, 11, 37] ⟨9769, 13, [(2, 3), (3, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_12197 : Nat.Prime 12197 := by
  apply nodeValid_prime [2, 3049] ⟨12197, 2, [(2, 2), (3049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3049
  · decide +kernel

theorem prime_13789 : Nat.Prime 13789 := by
  apply nodeValid_prime [2, 3, 383] ⟨13789, 7, [(2, 2), (3, 2), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_383
  · decide +kernel

theorem prime_14639 : Nat.Prime 14639 := by
  apply nodeValid_prime [2, 13, 563] ⟨14639, 11, [(2, 1), (13, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_563
  · decide +kernel

theorem prime_17729 : Nat.Prime 17729 := by
  apply nodeValid_prime [2, 277] ⟨17729, 3, [(2, 6), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_277
  · decide +kernel

theorem prime_18731 : Nat.Prime 18731 := by
  apply nodeValid_prime [2, 5, 1873] ⟨18731, 2, [(2, 1), (5, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1873
  · decide +kernel

theorem prime_21347 : Nat.Prime 21347 := by
  apply nodeValid_prime [2, 13, 821] ⟨21347, 2, [(2, 1), (13, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_821
  · decide +kernel

theorem prime_21871 : Nat.Prime 21871 := by
  apply nodeValid_prime [2, 3, 5] ⟨21871, 6, [(2, 1), (3, 7), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_22031 : Nat.Prime 22031 := by
  apply nodeValid_prime [2, 5, 2203] ⟨22031, 7, [(2, 1), (5, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2203
  · decide +kernel

theorem prime_22651 : Nat.Prime 22651 := by
  apply nodeValid_prime [2, 3, 5, 151] ⟨22651, 3, [(2, 1), (3, 1), (5, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
  · decide +kernel

theorem prime_23269 : Nat.Prime 23269 := by
  apply nodeValid_prime [2, 3, 7, 277] ⟨23269, 6, [(2, 2), (3, 1), (7, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_27743 : Nat.Prime 27743 := by
  apply nodeValid_prime [2, 11, 13, 97] ⟨27743, 5, [(2, 1), (11, 1), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_29573 : Nat.Prime 29573 := by
  apply nodeValid_prime [2, 7393] ⟨29573, 2, [(2, 2), (7393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7393
  · decide +kernel

theorem prime_30319 : Nat.Prime 30319 := by
  apply nodeValid_prime [2, 3, 31, 163] ⟨30319, 3, [(2, 1), (3, 1), (31, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_163
  · decide +kernel

theorem prime_35521 : Nat.Prime 35521 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨35521, 7, [(2, 6), (3, 1), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_36451 : Nat.Prime 36451 := by
  apply nodeValid_prime [2, 3, 5] ⟨36451, 7, [(2, 1), (3, 6), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_39301 : Nat.Prime 39301 := by
  apply nodeValid_prime [2, 3, 5, 131] ⟨39301, 7, [(2, 2), (3, 1), (5, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
  · decide +kernel

theorem prime_44657 : Nat.Prime 44657 := by
  apply nodeValid_prime [2, 2791] ⟨44657, 3, [(2, 4), (2791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2791
  · decide +kernel

theorem prime_46589 : Nat.Prime 46589 := by
  apply nodeValid_prime [2, 19, 613] ⟨46589, 2, [(2, 2), (19, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_613
  · decide +kernel

theorem prime_48733 : Nat.Prime 48733 := by
  apply nodeValid_prime [2, 3, 31, 131] ⟨48733, 2, [(2, 2), (3, 1), (31, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_131
  · decide +kernel

theorem prime_56417 : Nat.Prime 56417 := by
  apply nodeValid_prime [2, 41, 43] ⟨56417, 3, [(2, 5), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_67589 : Nat.Prime 67589 := by
  apply nodeValid_prime [2, 61, 277] ⟨67589, 2, [(2, 2), (61, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_277
  · decide +kernel

theorem prime_73061 : Nat.Prime 73061 := by
  apply nodeValid_prime [2, 5, 13, 281] ⟨73061, 2, [(2, 2), (5, 1), (13, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_281
  · decide +kernel

theorem prime_77419 : Nat.Prime 77419 := by
  apply nodeValid_prime [2, 3, 11, 17, 23] ⟨77419, 2, [(2, 1), (3, 2), (11, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_90917 : Nat.Prime 90917 := by
  apply nodeValid_prime [2, 7, 17, 191] ⟨90917, 2, [(2, 2), (7, 1), (17, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_191
  · decide +kernel

theorem prime_93179 : Nat.Prime 93179 := by
  apply nodeValid_prime [2, 46589] ⟨93179, 2, [(2, 1), (46589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46589
  · decide +kernel

theorem prime_94823 : Nat.Prime 94823 := by
  apply nodeValid_prime [2, 7, 13, 521] ⟨94823, 5, [(2, 1), (7, 1), (13, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_521
  · decide +kernel

theorem prime_113969 : Nat.Prime 113969 := by
  apply nodeValid_prime [2, 17, 419] ⟨113969, 3, [(2, 4), (17, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_419
  · decide +kernel

theorem prime_122041 : Nat.Prime 122041 := by
  apply nodeValid_prime [2, 3, 5, 113] ⟨122041, 7, [(2, 3), (3, 3), (5, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_136753 : Nat.Prime 136753 := by
  apply nodeValid_prime [2, 3, 7, 11, 37] ⟨136753, 5, [(2, 4), (3, 1), (7, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_149027 : Nat.Prime 149027 := by
  apply nodeValid_prime [2, 269, 277] ⟨149027, 2, [(2, 1), (269, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_277
  · decide +kernel

theorem prime_192263 : Nat.Prime 192263 := by
  apply nodeValid_prime [2, 7, 31, 443] ⟨192263, 7, [(2, 1), (7, 1), (31, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_443
  · decide +kernel

theorem prime_193201 : Nat.Prime 193201 := by
  apply nodeValid_prime [2, 3, 5, 7, 23] ⟨193201, 11, [(2, 4), (3, 1), (5, 2), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_219547 : Nat.Prime 219547 := by
  apply nodeValid_prime [2, 3, 12197] ⟨219547, 3, [(2, 1), (3, 2), (12197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12197
  · decide +kernel

theorem prime_242659 : Nat.Prime 242659 := by
  apply nodeValid_prime [2, 3, 13, 17, 61] ⟨242659, 2, [(2, 1), (3, 2), (13, 1), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_306139 : Nat.Prime 306139 := by
  apply nodeValid_prime [2, 3, 7, 37, 197] ⟨306139, 11, [(2, 1), (3, 1), (7, 1), (37, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_197
  · decide +kernel

theorem prime_340063 : Nat.Prime 340063 := by
  apply nodeValid_prime [2, 3, 19, 157] ⟨340063, 5, [(2, 1), (3, 1), (19, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_157
  · decide +kernel

theorem prime_367561 : Nat.Prime 367561 := by
  apply nodeValid_prime [2, 3, 5, 1021] ⟨367561, 7, [(2, 3), (3, 2), (5, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1021
  · decide +kernel

theorem prime_370661 : Nat.Prime 370661 := by
  apply nodeValid_prime [2, 5, 43, 431] ⟨370661, 3, [(2, 2), (5, 1), (43, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_431
  · decide +kernel

theorem prime_374741 : Nat.Prime 374741 := by
  apply nodeValid_prime [2, 5, 41, 457] ⟨374741, 2, [(2, 2), (5, 1), (41, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_457
  · decide +kernel

theorem prime_513173 : Nat.Prime 513173 := by
  apply nodeValid_prime [2, 11, 107, 109] ⟨513173, 2, [(2, 2), (11, 1), (107, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_107
    · exact prime_109
  · decide +kernel

theorem prime_529381 : Nat.Prime 529381 := by
  apply nodeValid_prime [2, 3, 5, 17, 173] ⟨529381, 2, [(2, 2), (3, 2), (5, 1), (17, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_173
  · decide +kernel

theorem prime_539843 : Nat.Prime 539843 := by
  apply nodeValid_prime [2, 47, 5743] ⟨539843, 2, [(2, 1), (47, 1), (5743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_5743
  · decide +kernel

theorem prime_634709 : Nat.Prime 634709 := by
  apply nodeValid_prime [2, 23, 6899] ⟨634709, 3, [(2, 2), (23, 1), (6899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_6899
  · decide +kernel

theorem prime_650227 : Nat.Prime 650227 := by
  apply nodeValid_prime [2, 3, 307, 353] ⟨650227, 2, [(2, 1), (3, 1), (307, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_353
  · decide +kernel

theorem prime_656741 : Nat.Prime 656741 := by
  apply nodeValid_prime [2, 5, 7, 4691] ⟨656741, 2, [(2, 2), (5, 1), (7, 1), (4691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_4691
  · decide +kernel

theorem prime_673193 : Nat.Prime 673193 := by
  apply nodeValid_prime [2, 13, 6473] ⟨673193, 3, [(2, 3), (13, 1), (6473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_6473
  · decide +kernel

theorem prime_692191 : Nat.Prime 692191 := by
  apply nodeValid_prime [2, 3, 5, 7691] ⟨692191, 11, [(2, 1), (3, 2), (5, 1), (7691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7691
  · decide +kernel

theorem prime_832291 : Nat.Prime 832291 := by
  apply nodeValid_prime [2, 3, 5, 27743] ⟨832291, 2, [(2, 1), (3, 1), (5, 1), (27743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27743
  · decide +kernel

theorem prime_950071 : Nat.Prime 950071 := by
  apply nodeValid_prime [2, 3, 5, 11, 2879] ⟨950071, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (2879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2879
  · decide +kernel

theorem prime_953983 : Nat.Prime 953983 := by
  apply nodeValid_prime [2, 3, 52999] ⟨953983, 5, [(2, 1), (3, 2), (52999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52999
  · decide +kernel

theorem prime_1319933 : Nat.Prime 1319933 := by
  apply nodeValid_prime [2, 79, 4177] ⟨1319933, 2, [(2, 2), (79, 1), (4177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_4177
  · decide +kernel

theorem prime_1354009 : Nat.Prime 1354009 := by
  apply nodeValid_prime [2, 3, 56417] ⟨1354009, 11, [(2, 3), (3, 1), (56417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56417
  · decide +kernel

theorem prime_1378373 : Nat.Prime 1378373 := by
  apply nodeValid_prime [2, 509, 677] ⟨1378373, 2, [(2, 2), (509, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_677
  · decide +kernel

theorem prime_1826323 : Nat.Prime 1826323 := by
  apply nodeValid_prime [2, 3, 79, 3853] ⟨1826323, 2, [(2, 1), (3, 1), (79, 1), (3853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_3853
  · decide +kernel

theorem prime_2248447 : Nat.Prime 2248447 := by
  apply nodeValid_prime [2, 3, 374741] ⟨2248447, 3, [(2, 1), (3, 1), (374741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_374741
  · decide +kernel

theorem prime_2332937 : Nat.Prime 2332937 := by
  apply nodeValid_prime [2, 23, 31, 409] ⟨2332937, 3, [(2, 3), (23, 1), (31, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_409
  · decide +kernel

theorem prime_2510513 : Nat.Prime 2510513 := by
  apply nodeValid_prime [2, 41, 43, 89] ⟨2510513, 3, [(2, 4), (41, 1), (43, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_43
    · exact prime_89
  · decide +kernel

theorem prime_2719141 : Nat.Prime 2719141 := by
  apply nodeValid_prime [2, 3, 5, 45319] ⟨2719141, 7, [(2, 2), (3, 1), (5, 1), (45319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_45319
  · decide +kernel

theorem prime_2825413 : Nat.Prime 2825413 := by
  apply nodeValid_prime [2, 3, 23, 29, 353] ⟨2825413, 2, [(2, 2), (3, 1), (23, 1), (29, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_29
    · exact prime_353
  · decide +kernel

theorem prime_3079039 : Nat.Prime 3079039 := by
  apply nodeValid_prime [2, 3, 513173] ⟨3079039, 3, [(2, 1), (3, 1), (513173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_513173
  · decide +kernel

theorem prime_3194951 : Nat.Prime 3194951 := by
  apply nodeValid_prime [2, 5, 11, 37, 157] ⟨3194951, 11, [(2, 1), (5, 2), (11, 1), (37, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_157
  · decide +kernel

theorem prime_3239059 : Nat.Prime 3239059 := by
  apply nodeValid_prime [2, 3, 539843] ⟨3239059, 2, [(2, 1), (3, 1), (539843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_539843
  · decide +kernel

theorem prime_3901363 : Nat.Prime 3901363 := by
  apply nodeValid_prime [2, 3, 650227] ⟨3901363, 5, [(2, 1), (3, 1), (650227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_650227
  · decide +kernel

theorem prime_4274911 : Nat.Prime 4274911 := by
  apply nodeValid_prime [2, 3, 5, 71, 223] ⟨4274911, 7, [(2, 1), (3, 3), (5, 1), (71, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_223
  · decide +kernel

theorem prime_4573171 : Nat.Prime 4573171 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 61] ⟨4573171, 7, [(2, 1), (3, 2), (5, 1), (7, 2), (17, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_61
  · decide +kernel

theorem prime_5723899 : Nat.Prime 5723899 := by
  apply nodeValid_prime [2, 3, 953983] ⟨5723899, 2, [(2, 1), (3, 1), (953983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_953983
  · decide +kernel

theorem prime_6997343 : Nat.Prime 6997343 := by
  apply nodeValid_prime [2, 11, 73, 4357] ⟨6997343, 5, [(2, 1), (11, 1), (73, 1), (4357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_4357
  · decide +kernel

theorem prime_8044693 : Nat.Prime 8044693 := by
  apply nodeValid_prime [2, 3, 41, 83, 197] ⟨8044693, 5, [(2, 2), (3, 1), (41, 1), (83, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_83
    · exact prime_197
  · decide +kernel

theorem prime_8583989 : Nat.Prime 8583989 := by
  apply nodeValid_prime [2, 7, 281, 1091] ⟨8583989, 2, [(2, 2), (7, 1), (281, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_281
    · exact prime_1091
  · decide +kernel

theorem prime_11647633 : Nat.Prime 11647633 := by
  apply nodeValid_prime [2, 3, 242659] ⟨11647633, 5, [(2, 4), (3, 1), (242659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_242659
  · decide +kernel

theorem prime_18411373 : Nat.Prime 18411373 := by
  apply nodeValid_prime [2, 3, 7, 73061] ⟨18411373, 2, [(2, 2), (3, 2), (7, 1), (73061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73061
  · decide +kernel

theorem prime_18657689 : Nat.Prime 18657689 := by
  apply nodeValid_prime [2, 7, 59, 5647] ⟨18657689, 3, [(2, 3), (7, 1), (59, 1), (5647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_5647
  · decide +kernel

theorem prime_23915173 : Nat.Prime 23915173 := by
  apply nodeValid_prime [2, 3, 37, 61, 883] ⟨23915173, 2, [(2, 2), (3, 1), (37, 1), (61, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_61
    · exact prime_883
  · decide +kernel

theorem prime_26116367 : Nat.Prime 26116367 := by
  apply nodeValid_prime [2, 947, 13789] ⟨26116367, 5, [(2, 1), (947, 1), (13789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_947
    · exact prime_13789
  · decide +kernel

theorem prime_26148781 : Nat.Prime 26148781 := by
  apply nodeValid_prime [2, 3, 5, 7, 20753] ⟨26148781, 6, [(2, 2), (3, 2), (5, 1), (7, 1), (20753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_20753
  · decide +kernel

theorem prime_30406601 : Nat.Prime 30406601 := by
  apply nodeValid_prime [2, 5, 7, 37, 587] ⟨30406601, 12, [(2, 3), (5, 2), (7, 1), (37, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_587
  · decide +kernel

theorem prime_32390591 : Nat.Prime 32390591 := by
  apply nodeValid_prime [2, 5, 3239059] ⟨32390591, 7, [(2, 1), (5, 1), (3239059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3239059
  · decide +kernel

theorem prime_34607009 : Nat.Prime 34607009 := by
  apply nodeValid_prime [2, 61, 17729] ⟨34607009, 3, [(2, 5), (61, 1), (17729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_17729
  · decide +kernel

theorem prime_48454657 : Nat.Prime 48454657 := by
  apply nodeValid_prime [2, 3, 15773] ⟨48454657, 5, [(2, 10), (3, 1), (15773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15773
  · decide +kernel

theorem prime_51471029 : Nat.Prime 51471029 := by
  apply nodeValid_prime [2, 7, 79, 23269] ⟨51471029, 3, [(2, 2), (7, 1), (79, 1), (23269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_23269
  · decide +kernel

theorem prime_57018763 : Nat.Prime 57018763 := by
  apply nodeValid_prime [2, 3, 193, 5471] ⟨57018763, 2, [(2, 1), (3, 3), (193, 1), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_5471
  · decide +kernel

theorem prime_62234413 : Nat.Prime 62234413 := by
  apply nodeValid_prime [2, 3, 23, 443, 509] ⟨62234413, 2, [(2, 2), (3, 1), (23, 1), (443, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_443
    · exact prime_509
  · decide +kernel

theorem prime_75315391 : Nat.Prime 75315391 := by
  apply nodeValid_prime [2, 3, 5, 2510513] ⟨75315391, 6, [(2, 1), (3, 1), (5, 1), (2510513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2510513
  · decide +kernel

theorem prime_81002863 : Nat.Prime 81002863 := by
  apply nodeValid_prime [2, 3, 1153, 1301] ⟨81002863, 5, [(2, 1), (3, 3), (1153, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1153
    · exact prime_1301
  · decide +kernel

theorem prime_98995213 : Nat.Prime 98995213 := by
  apply nodeValid_prime [2, 3, 29, 94823] ⟨98995213, 5, [(2, 2), (3, 2), (29, 1), (94823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_94823
  · decide +kernel

theorem prime_164844389 : Nat.Prime 164844389 := by
  apply nodeValid_prime [2, 67, 193, 3187] ⟨164844389, 2, [(2, 2), (67, 1), (193, 1), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_193
    · exact prime_3187
  · decide +kernel

theorem prime_177740369 : Nat.Prime 177740369 := by
  apply nodeValid_prime [2, 13, 281, 3041] ⟨177740369, 6, [(2, 4), (13, 1), (281, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_281
    · exact prime_3041
  · decide +kernel

theorem prime_184113731 : Nat.Prime 184113731 := by
  apply nodeValid_prime [2, 5, 18411373] ⟨184113731, 2, [(2, 1), (5, 1), (18411373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18411373
  · decide +kernel

theorem prime_194612567 : Nat.Prime 194612567 := by
  apply nodeValid_prime [2, 17, 5723899] ⟨194612567, 5, [(2, 1), (17, 1), (5723899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_5723899
  · decide +kernel

theorem prime_241614281 : Nat.Prime 241614281 := by
  apply nodeValid_prime [2, 5, 53, 113969] ⟨241614281, 6, [(2, 3), (5, 1), (53, 1), (113969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_113969
  · decide +kernel

theorem prime_342612667 : Nat.Prime 342612667 := by
  apply nodeValid_prime [2, 3, 11, 192263] ⟨342612667, 2, [(2, 1), (3, 4), (11, 1), (192263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_192263
  · decide +kernel

theorem prime_350351213 : Nat.Prime 350351213 := by
  apply nodeValid_prime [2, 31, 2825413] ⟨350351213, 2, [(2, 2), (31, 1), (2825413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2825413
  · decide +kernel

theorem prime_366647219 : Nat.Prime 366647219 := by
  apply nodeValid_prime [2, 7, 19, 1378373] ⟨366647219, 2, [(2, 1), (7, 1), (19, 1), (1378373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_1378373
  · decide +kernel

theorem prime_391184707 : Nat.Prime 391184707 := by
  apply nodeValid_prime [2, 3, 11, 271, 21871] ⟨391184707, 2, [(2, 1), (3, 1), (11, 1), (271, 1), (21871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_271
    · exact prime_21871
  · decide +kernel

theorem prime_427193479 : Nat.Prime 427193479 := by
  apply nodeValid_prime [2, 3, 487, 48733] ⟨427193479, 6, [(2, 1), (3, 2), (487, 1), (48733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
    · exact prime_48733
  · decide +kernel

theorem prime_436728151 : Nat.Prime 436728151 := by
  apply nodeValid_prime [2, 3, 5, 241, 4027] ⟨436728151, 3, [(2, 1), (3, 2), (5, 2), (241, 1), (4027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
    · exact prime_4027
  · decide +kernel

theorem prime_484546571 : Nat.Prime 484546571 := by
  apply nodeValid_prime [2, 5, 48454657] ⟨484546571, 2, [(2, 1), (5, 1), (48454657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_48454657
  · decide +kernel

theorem prime_501764953 : Nat.Prime 501764953 := by
  apply nodeValid_prime [2, 3, 13, 71, 22651] ⟨501764953, 5, [(2, 3), (3, 1), (13, 1), (71, 1), (22651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_22651
  · decide +kernel

theorem prime_804944027 : Nat.Prime 804944027 := by
  apply nodeValid_prime [2, 179, 2248447] ⟨804944027, 2, [(2, 1), (179, 1), (2248447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_2248447
  · decide +kernel

theorem prime_937649191 : Nat.Prime 937649191 := by
  apply nodeValid_prime [2, 3, 5, 37, 353, 2393] ⟨937649191, 3, [(2, 1), (3, 1), (5, 1), (37, 1), (353, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_353
    · exact prime_2393
  · decide +kernel

theorem prime_1219618093 : Nat.Prime 1219618093 := by
  apply nodeValid_prime [2, 3, 7, 11, 1319933] ⟨1219618093, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (1319933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1319933
  · decide +kernel

theorem prime_1450579327 : Nat.Prime 1450579327 := by
  apply nodeValid_prime [2, 3, 7, 283, 122041] ⟨1450579327, 13, [(2, 1), (3, 1), (7, 1), (283, 1), (122041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
    · exact prime_122041
  · decide +kernel

theorem prime_1677043783 : Nat.Prime 1677043783 := by
  apply nodeValid_prime [2, 3, 4229, 22031] ⟨1677043783, 3, [(2, 1), (3, 2), (4229, 1), (22031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4229
    · exact prime_22031
  · decide +kernel

theorem prime_2488365167 : Nat.Prime 2488365167 := by
  apply nodeValid_prime [2, 7, 177740369] ⟨2488365167, 5, [(2, 1), (7, 1), (177740369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_177740369
  · decide +kernel

theorem prime_2919661639 : Nat.Prime 2919661639 := by
  apply nodeValid_prime [2, 3, 19, 37, 692191] ⟨2919661639, 11, [(2, 1), (3, 1), (19, 1), (37, 1), (692191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_692191
  · decide +kernel

theorem prime_4404449921 : Nat.Prime 4404449921 := by
  apply nodeValid_prime [2, 5, 13, 529381] ⟨4404449921, 6, [(2, 7), (5, 1), (13, 1), (529381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_529381
  · decide +kernel

theorem prime_4829664163 : Nat.Prime 4829664163 := by
  apply nodeValid_prime [2, 3, 804944027] ⟨4829664163, 3, [(2, 1), (3, 1), (804944027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_804944027
  · decide +kernel

theorem prime_4878472373 : Nat.Prime 4878472373 := by
  apply nodeValid_prime [2, 1219618093] ⟨4878472373, 2, [(2, 2), (1219618093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1219618093
  · decide +kernel

theorem prime_5945054113 : Nat.Prime 5945054113 := by
  apply nodeValid_prime [2, 3, 967, 21347] ⟨5945054113, 5, [(2, 5), (3, 2), (967, 1), (21347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
    · exact prime_21347
  · decide +kernel

theorem prime_7093240631 : Nat.Prime 7093240631 := by
  apply nodeValid_prime [2, 5, 7, 331, 306139] ⟨7093240631, 7, [(2, 1), (5, 1), (7, 1), (331, 1), (306139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_331
    · exact prime_306139
  · decide +kernel

theorem prime_8028239249 : Nat.Prime 8028239249 := by
  apply nodeValid_prime [2, 501764953] ⟨8028239249, 3, [(2, 4), (501764953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_501764953
  · decide +kernel

theorem prime_10523449903 : Nat.Prime 10523449903 := by
  apply nodeValid_prime [2, 3, 7, 2689, 93179] ⟨10523449903, 3, [(2, 1), (3, 1), (7, 1), (2689, 1), (93179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2689
    · exact prime_93179
  · decide +kernel

theorem prime_12598210847 : Nat.Prime 12598210847 := by
  apply nodeValid_prime [2, 13, 484546571] ⟨12598210847, 5, [(2, 1), (13, 1), (484546571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_484546571
  · decide +kernel

theorem prime_13318091239 : Nat.Prime 13318091239 := by
  apply nodeValid_prime [2, 3, 73, 30406601] ⟨13318091239, 3, [(2, 1), (3, 1), (73, 1), (30406601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_30406601
  · decide +kernel

theorem prime_28101210937 : Nat.Prime 28101210937 := by
  apply nodeValid_prime [2, 3, 17, 137, 29573] ⟨28101210937, 5, [(2, 3), (3, 1), (17, 2), (137, 1), (29573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_137
    · exact prime_29573
  · decide +kernel

theorem prime_34597181819 : Nat.Prime 34597181819 := by
  apply nodeValid_prime [2, 347, 5557, 8971] ⟨34597181819, 2, [(2, 1), (347, 1), (5557, 1), (8971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_5557
    · exact prime_8971
  · decide +kernel

theorem prime_69963217781 : Nat.Prime 69963217781 := by
  apply nodeValid_prime [2, 5, 19, 184113731] ⟨69963217781, 2, [(2, 2), (5, 1), (19, 1), (184113731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_184113731
  · decide +kernel

theorem prime_84768838351 : Nat.Prime 84768838351 := by
  apply nodeValid_prime [2, 3, 5, 7, 97, 832291] ⟨84768838351, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (97, 1), (832291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_97
    · exact prime_832291
  · decide +kernel

theorem prime_105234499031 : Nat.Prime 105234499031 := by
  apply nodeValid_prime [2, 5, 10523449903] ⟨105234499031, 14, [(2, 1), (5, 1), (10523449903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10523449903
  · decide +kernel

theorem prime_106252611587 : Nat.Prime 106252611587 := by
  apply nodeValid_prime [2, 11, 4829664163] ⟨106252611587, 2, [(2, 1), (11, 1), (4829664163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4829664163
  · decide +kernel

theorem prime_138580319441 : Nat.Prime 138580319441 := by
  apply nodeValid_prime [2, 5, 23, 75315391] ⟨138580319441, 3, [(2, 4), (5, 1), (23, 1), (75315391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_75315391
  · decide +kernel

theorem prime_140119461113 : Nat.Prime 140119461113 := by
  apply nodeValid_prime [2, 41, 427193479] ⟨140119461113, 5, [(2, 3), (41, 1), (427193479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_427193479
  · decide +kernel

theorem prime_140119462061 : Nat.Prime 140119462061 := by
  apply nodeValid_prime [2, 5, 263, 293, 90917] ⟨140119462061, 2, [(2, 2), (5, 1), (263, 1), (293, 1), (90917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
    · exact prime_293
    · exact prime_90917
  · decide +kernel

theorem prime_211922095573 : Nat.Prime 211922095573 := by
  apply nodeValid_prime [2, 3, 11, 29, 3373, 5471] ⟨211922095573, 2, [(2, 2), (3, 2), (11, 1), (29, 1), (3373, 1), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_3373
    · exact prime_5471
  · decide +kernel

theorem prime_414591952739 : Nat.Prime 414591952739 := by
  apply nodeValid_prime [2, 71, 2919661639] ⟨414591952739, 2, [(2, 1), (71, 1), (2919661639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2919661639
  · decide +kernel

theorem prime_418622804081 : Nat.Prime 418622804081 := by
  apply nodeValid_prime [2, 5, 13, 37, 73, 149027] ⟨418622804081, 3, [(2, 4), (5, 1), (13, 1), (37, 1), (73, 1), (149027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_73
    · exact prime_149027
  · decide +kernel

theorem prime_420358383383 : Nat.Prime 420358383383 := by
  apply nodeValid_prime [2, 7, 613, 6997343] ⟨420358383383, 5, [(2, 1), (7, 2), (613, 1), (6997343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_613
    · exact prime_6997343
  · decide +kernel

theorem prime_426763965629 : Nat.Prime 426763965629 := by
  apply nodeValid_prime [2, 7, 11, 13, 17, 151, 41521] ⟨426763965629, 10, [(2, 2), (7, 1), (11, 1), (13, 1), (17, 1), (151, 1), (41521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_151
    · exact prime_41521
  · decide +kernel

theorem prime_427349527613 : Nat.Prime 427349527613 := by
  apply nodeValid_prime [2, 7, 23, 109, 1289, 4723] ⟨427349527613, 2, [(2, 2), (7, 1), (23, 1), (109, 1), (1289, 1), (4723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_109
    · exact prime_1289
    · exact prime_4723
  · decide +kernel

theorem prime_828036574297 : Nat.Prime 828036574297 := by
  apply nodeValid_prime [2, 3, 79, 436728151] ⟨828036574297, 5, [(2, 3), (3, 1), (79, 1), (436728151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_436728151
  · decide +kernel

theorem prime_828036584971 : Nat.Prime 828036584971 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 127, 1826323] ⟨828036584971, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (127, 1), (1826323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_127
    · exact prime_1826323
  · decide +kernel

theorem prime_828036585149 : Nat.Prime 828036585149 := by
  apply nodeValid_prime [2, 47, 4404449921] ⟨828036585149, 2, [(2, 2), (47, 1), (4404449921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_4404449921
  · decide +kernel

theorem prime_829183904089 : Nat.Prime 829183904089 := by
  apply nodeValid_prime [2, 3, 349, 98995213] ⟨829183904089, 11, [(2, 3), (3, 1), (349, 1), (98995213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_98995213
  · decide +kernel

theorem prime_829183905479 : Nat.Prime 829183905479 := by
  apply nodeValid_prime [2, 414591952739] ⟨829183905479, 13, [(2, 1), (414591952739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_414591952739
  · decide +kernel

theorem prime_829183935641 : Nat.Prime 829183935641 := by
  apply nodeValid_prime [2, 5, 599, 34607009] ⟨829183935641, 3, [(2, 3), (5, 1), (599, 1), (34607009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_599
    · exact prime_34607009
  · decide +kernel

theorem prime_830332363657 : Nat.Prime 830332363657 := by
  apply nodeValid_prime [2, 3, 34597181819] ⟨830332363657, 5, [(2, 3), (3, 1), (34597181819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34597181819
  · decide +kernel

theorem prime_830332365787 : Nat.Prime 830332365787 := by
  apply nodeValid_prime [2, 3, 7, 11, 131, 4573171] ⟨830332365787, 2, [(2, 1), (3, 2), (7, 1), (11, 1), (131, 1), (4573171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_131
    · exact prime_4573171
  · decide +kernel

theorem prime_830332374811 : Nat.Prime 830332374811 := by
  apply nodeValid_prime [2, 3, 5, 79, 350351213] ⟨830332374811, 3, [(2, 1), (3, 1), (5, 1), (79, 1), (350351213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_350351213
  · decide +kernel

theorem prime_831481890739 : Nat.Prime 831481890739 := by
  apply nodeValid_prime [2, 3, 35521, 3901363] ⟨831481890739, 2, [(2, 1), (3, 1), (35521, 1), (3901363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35521
    · exact prime_3901363
  · decide +kernel

theorem prime_831481915903 : Nat.Prime 831481915903 := by
  apply nodeValid_prime [2, 3, 11, 12598210847] ⟨831481915903, 5, [(2, 1), (3, 1), (11, 1), (12598210847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_12598210847
  · decide +kernel

theorem prime_831481916647 : Nat.Prime 831481916647 := by
  apply nodeValid_prime [2, 3, 138580319441] ⟨831481916647, 3, [(2, 1), (3, 1), (138580319441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_138580319441
  · decide +kernel

theorem prime_832632481609 : Nat.Prime 832632481609 := by
  apply nodeValid_prime [2, 3, 37, 937649191] ⟨832632481609, 7, [(2, 3), (3, 1), (37, 1), (937649191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_937649191
  · decide +kernel

theorem prime_832632532247 : Nat.Prime 832632532247 := by
  apply nodeValid_prime [2, 12853, 32390591] ⟨832632532247, 5, [(2, 1), (12853, 1), (32390591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_12853
    · exact prime_32390591
  · decide +kernel

theorem prime_832632533699 : Nat.Prime 832632533699 := by
  apply nodeValid_prime [2, 7, 41, 1450579327] ⟨832632533699, 2, [(2, 1), (7, 1), (41, 1), (1450579327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_1450579327
  · decide +kernel

theorem prime_833784146677 : Nat.Prime 833784146677 := by
  apply nodeValid_prime [2, 3, 13, 31, 340063] ⟨833784146677, 5, [(2, 2), (3, 2), (13, 3), (31, 1), (340063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_340063
  · decide +kernel

theorem prime_833784160673 : Nat.Prime 833784160673 := by
  apply nodeValid_prime [2, 2237, 11647633] ⟨833784160673, 3, [(2, 5), (2237, 1), (11647633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2237
    · exact prime_11647633
  · decide +kernel

theorem prime_833784161293 : Nat.Prime 833784161293 := by
  apply nodeValid_prime [2, 3, 2879, 8044693] ⟨833784161293, 2, [(2, 2), (3, 2), (2879, 1), (8044693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2879
    · exact prime_8044693
  · decide +kernel

theorem prime_834936881897 : Nat.Prime 834936881897 := by
  apply nodeValid_prime [2, 13, 8028239249] ⟨834936881897, 3, [(2, 3), (13, 1), (8028239249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8028239249
  · decide +kernel

theorem prime_834936883483 : Nat.Prime 834936883483 := by
  apply nodeValid_prime [2, 3, 13, 28879, 370661] ⟨834936883483, 2, [(2, 1), (3, 1), (13, 1), (28879, 1), (370661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_28879
    · exact prime_370661
  · decide +kernel

theorem prime_834936884809 : Nat.Prime 834936884809 := by
  apply nodeValid_prime [2, 3, 13, 43, 62234413] ⟨834936884809, 14, [(2, 3), (3, 1), (13, 1), (43, 1), (62234413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_62234413
  · decide +kernel

theorem prime_836090696113 : Nat.Prime 836090696113 := by
  apply nodeValid_prime [2, 3, 7, 2488365167] ⟨836090696113, 10, [(2, 4), (3, 1), (7, 1), (2488365167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2488365167
  · decide +kernel

theorem prime_836090740939 : Nat.Prime 836090740939 := by
  apply nodeValid_prime [2, 3, 219547, 634709] ⟨836090740939, 3, [(2, 1), (3, 1), (219547, 1), (634709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_219547
    · exact prime_634709
  · decide +kernel

theorem prime_836090741009 : Nat.Prime 836090741009 := by
  apply nodeValid_prime [2, 317, 164844389] ⟨836090741009, 3, [(2, 4), (317, 1), (164844389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_164844389
  · decide +kernel

theorem prime_837245591969 : Nat.Prime 837245591969 := by
  apply nodeValid_prime [2, 17, 19, 81002863] ⟨837245591969, 6, [(2, 5), (17, 1), (19, 1), (81002863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_81002863
  · decide +kernel

theorem prime_837245607769 : Nat.Prime 837245607769 := by
  apply nodeValid_prime [2, 3, 5563, 77419] ⟨837245607769, 11, [(2, 3), (3, 5), (5563, 1), (77419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5563
    · exact prime_77419
  · decide +kernel

theorem prime_837245608163 : Nat.Prime 837245608163 := by
  apply nodeValid_prime [2, 418622804081] ⟨837245608163, 2, [(2, 1), (418622804081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_418622804081
  · decide +kernel

theorem prime_838401554803 : Nat.Prime 838401554803 := by
  apply nodeValid_prime [2, 3, 7, 21011, 950071] ⟨838401554803, 5, [(2, 1), (3, 1), (7, 1), (21011, 1), (950071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_21011
    · exact prime_950071
  · decide +kernel

theorem prime_838401555071 : Nat.Prime 838401555071 := by
  apply nodeValid_prime [2, 5, 347, 241614281] ⟨838401555071, 11, [(2, 1), (5, 1), (347, 1), (241614281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_347
    · exact prime_241614281
  · decide +kernel

theorem prime_838401567313 : Nat.Prime 838401567313 := by
  apply nodeValid_prime [2, 3, 7487, 2332937] ⟨838401567313, 5, [(2, 4), (3, 1), (7487, 1), (2332937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7487
    · exact prime_2332937
  · decide +kernel

theorem prime_839558613373 : Nat.Prime 839558613373 := by
  apply nodeValid_prime [2, 3, 69963217781] ⟨839558613373, 2, [(2, 2), (3, 1), (69963217781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_69963217781
  · decide +kernel

theorem prime_839558614039 : Nat.Prime 839558614039 := by
  apply nodeValid_prime [2, 3, 719, 194612567] ⟨839558614039, 3, [(2, 1), (3, 1), (719, 1), (194612567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
    · exact prime_194612567
  · decide +kernel

theorem prime_839558629669 : Nat.Prime 839558629669 := by
  apply nodeValid_prime [2, 3, 11, 23, 41, 761, 8863] ⟨839558629669, 10, [(2, 2), (3, 1), (11, 1), (23, 1), (41, 1), (761, 1), (8863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_41
    · exact prime_761
    · exact prime_8863
  · decide +kernel

theorem prime_840716766679 : Nat.Prime 840716766679 := by
  apply nodeValid_prime [2, 3, 140119461113] ⟨840716766679, 3, [(2, 1), (3, 1), (140119461113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_140119461113
  · decide +kernel

theorem prime_840716766767 : Nat.Prime 840716766767 := by
  apply nodeValid_prime [2, 420358383383] ⟨840716766767, 5, [(2, 1), (420358383383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_420358383383
  · decide +kernel

theorem prime_840716772367 : Nat.Prime 840716772367 := by
  apply nodeValid_prime [2, 3, 140119462061] ⟨840716772367, 3, [(2, 1), (3, 1), (140119462061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_140119462061
  · decide +kernel

theorem prime_841875978403 : Nat.Prime 841875978403 := by
  apply nodeValid_prime [2, 3, 14639, 3194951] ⟨841875978403, 14, [(2, 1), (3, 2), (14639, 1), (3194951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14639
    · exact prime_3194951
  · decide +kernel

theorem prime_841875979067 : Nat.Prime 841875979067 := by
  apply nodeValid_prime [2, 251, 1677043783] ⟨841875979067, 2, [(2, 1), (251, 1), (1677043783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_1677043783
  · decide +kernel

theorem prime_841875992249 : Nat.Prime 841875992249 := by
  apply nodeValid_prime [2, 105234499031] ⟨841875992249, 3, [(2, 3), (105234499031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_105234499031
  · decide +kernel

theorem prime_843036295993 : Nat.Prime 843036295993 := by
  apply nodeValid_prime [2, 3, 11, 19, 1229, 136753] ⟨843036295993, 5, [(2, 3), (3, 1), (11, 1), (19, 1), (1229, 1), (136753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_1229
    · exact prime_136753
  · decide +kernel

theorem prime_843036326761 : Nat.Prime 843036326761 := by
  apply nodeValid_prime [2, 3, 5, 269, 26116367] ⟨843036326761, 14, [(2, 3), (3, 1), (5, 1), (269, 1), (26116367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_269
    · exact prime_26116367
  · decide +kernel

theorem prime_843036328111 : Nat.Prime 843036328111 := by
  apply nodeValid_prime [2, 3, 5, 28101210937] ⟨843036328111, 6, [(2, 1), (3, 1), (5, 1), (28101210937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28101210937
  · decide +kernel

theorem prime_844197610931 : Nat.Prime 844197610931 := by
  apply nodeValid_prime [2, 5, 53, 103, 1583, 9769] ⟨844197610931, 2, [(2, 1), (5, 1), (53, 1), (103, 1), (1583, 1), (9769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_103
    · exact prime_1583
    · exact prime_9769
  · decide +kernel

theorem prime_844197611489 : Nat.Prime 844197611489 := by
  apply nodeValid_prime [2, 7, 11, 342612667] ⟨844197611489, 3, [(2, 5), (7, 1), (11, 1), (342612667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_342612667
  · decide +kernel

theorem prime_844197684047 : Nat.Prime 844197684047 := by
  apply nodeValid_prime [2, 71, 5945054113] ⟨844197684047, 5, [(2, 1), (71, 1), (5945054113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_5945054113
  · decide +kernel

theorem prime_845360159999 : Nat.Prime 845360159999 := by
  apply nodeValid_prime [2, 373, 3083, 367561] ⟨845360159999, 11, [(2, 1), (373, 1), (3083, 1), (367561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_3083
    · exact prime_367561
  · decide +kernel

theorem prime_845360180239 : Nat.Prime 845360180239 := by
  apply nodeValid_prime [2, 3, 7, 353, 57018763] ⟨845360180239, 3, [(2, 1), (3, 1), (7, 1), (353, 1), (57018763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_353
    · exact prime_57018763
  · decide +kernel

theorem prime_845360180297 : Nat.Prime 845360180297 := by
  apply nodeValid_prime [2, 2053, 51471029] ⟨845360180297, 3, [(2, 3), (2053, 1), (51471029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2053
    · exact prime_51471029
  · decide +kernel

theorem prime_846523705571 : Nat.Prime 846523705571 := by
  apply nodeValid_prime [2, 5, 83, 5279, 193201] ⟨846523705571, 2, [(2, 1), (5, 1), (83, 1), (5279, 1), (193201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_5279
    · exact prime_193201
  · decide +kernel

theorem prime_846523705949 : Nat.Prime 846523705949 := by
  apply nodeValid_prime [2, 541, 391184707] ⟨846523705949, 2, [(2, 2), (541, 1), (391184707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_541
    · exact prime_391184707
  · decide +kernel

theorem prime_846523718783 : Nat.Prime 846523718783 := by
  apply nodeValid_prime [2, 7, 44657, 1354009] ⟨846523718783, 5, [(2, 1), (7, 1), (44657, 1), (1354009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_44657
    · exact prime_1354009
  · decide +kernel

theorem prime_847688370329 : Nat.Prime 847688370329 := by
  apply nodeValid_prime [2, 17, 366647219] ⟨847688370329, 3, [(2, 3), (17, 2), (366647219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_366647219
  · decide +kernel

theorem prime_847688382293 : Nat.Prime 847688382293 := by
  apply nodeValid_prime [2, 211922095573] ⟨847688382293, 2, [(2, 2), (211922095573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_211922095573
  · decide +kernel

theorem prime_847688383511 : Nat.Prime 847688383511 := by
  apply nodeValid_prime [2, 5, 84768838351] ⟨847688383511, 13, [(2, 1), (5, 1), (84768838351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_84768838351
  · decide +kernel

theorem prime_848854103833 : Nat.Prime 848854103833 := by
  apply nodeValid_prime [2, 3, 7, 547, 3079039] ⟨848854103833, 5, [(2, 3), (3, 2), (7, 1), (547, 1), (3079039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_547
    · exact prime_3079039
  · decide +kernel

theorem prime_848854192727 : Nat.Prime 848854192727 := by
  apply nodeValid_prime [2, 103, 179, 1229, 18731] ⟨848854192727, 5, [(2, 1), (103, 1), (179, 1), (1229, 1), (18731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_179
    · exact prime_1229
    · exact prime_18731
  · decide +kernel

theorem prime_848854192903 : Nat.Prime 848854192903 := by
  apply nodeValid_prime [2, 3, 29, 4878472373] ⟨848854192903, 3, [(2, 1), (3, 1), (29, 1), (4878472373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_4878472373
  · decide +kernel

theorem prime_850020892481 : Nat.Prime 850020892481 := by
  apply nodeValid_prime [2, 5, 39301, 67589] ⟨850020892481, 3, [(2, 6), (5, 1), (39301, 1), (67589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_39301
    · exact prime_67589
  · decide +kernel

theorem prime_850020892697 : Nat.Prime 850020892697 := by
  apply nodeValid_prime [2, 106252611587] ⟨850020892697, 3, [(2, 3), (106252611587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_106252611587
  · decide +kernel

theorem prime_850020926737 : Nat.Prime 850020926737 := by
  apply nodeValid_prime [2, 3, 2063, 8583989] ⟨850020926737, 7, [(2, 4), (3, 1), (2063, 1), (8583989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2063
    · exact prime_8583989
  · decide +kernel

theorem prime_851188837417 : Nat.Prime 851188837417 := by
  apply nodeValid_prime [2, 3, 1483, 23915173] ⟨851188837417, 5, [(2, 3), (3, 1), (1483, 1), (23915173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1483
    · exact prime_23915173
  · decide +kernel

theorem prime_851188875281 : Nat.Prime 851188875281 := by
  apply nodeValid_prime [2, 5, 17, 953, 656741] ⟨851188875281, 3, [(2, 4), (5, 1), (17, 1), (953, 1), (656741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_953
    · exact prime_656741
  · decide +kernel

theorem prime_851188875721 : Nat.Prime 851188875721 := by
  apply nodeValid_prime [2, 3, 5, 7093240631] ⟨851188875721, 19, [(2, 3), (3, 1), (5, 1), (7093240631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7093240631
  · decide +kernel

theorem prime_852357839297 : Nat.Prime 852357839297 := by
  apply nodeValid_prime [2, 13318091239] ⟨852357839297, 3, [(2, 6), (13318091239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13318091239
  · decide +kernel

theorem prime_852357864277 : Nat.Prime 852357864277 := by
  apply nodeValid_prime [2, 3, 47, 18657689] ⟨852357864277, 2, [(2, 2), (3, 5), (47, 1), (18657689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_18657689
  · decide +kernel

theorem prime_852357865087 : Nat.Prime 852357865087 := by
  apply nodeValid_prime [2, 3, 7, 13, 1907, 30319] ⟨852357865087, 10, [(2, 1), (3, 4), (7, 1), (13, 1), (1907, 1), (30319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1907
    · exact prime_30319
  · decide +kernel

theorem prime_853527931259 : Nat.Prime 853527931259 := by
  apply nodeValid_prime [2, 426763965629] ⟨853527931259, 2, [(2, 1), (426763965629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_426763965629
  · decide +kernel

theorem prime_853527940663 : Nat.Prime 853527940663 := by
  apply nodeValid_prime [2, 3, 463, 8429, 36451] ⟨853527940663, 3, [(2, 1), (3, 1), (463, 1), (8429, 1), (36451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
    · exact prime_8429
    · exact prime_36451
  · decide +kernel

theorem prime_853527940841 : Nat.Prime 853527940841 := by
  apply nodeValid_prime [2, 5, 29, 1093, 673193] ⟨853527940841, 3, [(2, 3), (5, 1), (29, 1), (1093, 1), (673193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_1093
    · exact prime_673193
  · decide +kernel

theorem prime_854699055227 : Nat.Prime 854699055227 := by
  apply nodeValid_prime [2, 427349527613] ⟨854699055227, 2, [(2, 1), (427349527613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_427349527613
  · decide +kernel

theorem prime_854699055767 : Nat.Prime 854699055767 := by
  apply nodeValid_prime [2, 59, 277, 26148781] ⟨854699055767, 5, [(2, 1), (59, 1), (277, 1), (26148781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_277
    · exact prime_26148781
  · decide +kernel

theorem prime_854699115019 : Nat.Prime 854699115019 := by
  apply nodeValid_prime [2, 3, 7, 293, 1327, 7477] ⟨854699115019, 2, [(2, 1), (3, 1), (7, 2), (293, 1), (1327, 1), (7477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_293
    · exact prime_1327
    · exact prime_7477
  · decide +kernel

theorem prime_855871381489 : Nat.Prime 855871381489 := by
  apply nodeValid_prime [2, 3, 43, 97, 4274911] ⟨855871381489, 7, [(2, 4), (3, 1), (43, 1), (97, 1), (4274911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_97
    · exact prime_4274911
  · decide +kernel

theorem prime_855871382489 : Nat.Prime 855871382489 := by
  apply nodeValid_prime [2, 41, 109, 127, 233, 809] ⟨855871382489, 3, [(2, 3), (41, 1), (109, 1), (127, 1), (233, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_109
    · exact prime_127
    · exact prime_233
    · exact prime_809
  · decide +kernel

theorem prime_855871382879 : Nat.Prime 855871382879 := by
  apply nodeValid_prime [2, 337, 467, 2719141] ⟨855871382879, 7, [(2, 1), (337, 1), (467, 1), (2719141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_467
    · exact prime_2719141
  · decide +kernel

end Sude.Lucas.Generated
