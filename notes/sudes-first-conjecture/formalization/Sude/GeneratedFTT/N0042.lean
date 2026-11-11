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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2713 : Nat.Prime 2713 := by
  apply nodeValid_prime [2, 3, 113] ⟨2713, 5, [(2, 3), (3, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
  · decide +kernel

theorem prime_3433 : Nat.Prime 3433 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨3433, 5, [(2, 3), (3, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_3863 : Nat.Prime 3863 := by
  apply nodeValid_prime [2, 1931] ⟨3863, 5, [(2, 1), (1931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1931
  · decide +kernel

theorem prime_4283 : Nat.Prime 4283 := by
  apply nodeValid_prime [2, 2141] ⟨4283, 2, [(2, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2141
  · decide +kernel

theorem prime_4483 : Nat.Prime 4483 := by
  apply nodeValid_prime [2, 3, 83] ⟨4483, 2, [(2, 1), (3, 3), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_5333 : Nat.Prime 5333 := by
  apply nodeValid_prime [2, 31, 43] ⟨5333, 2, [(2, 2), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_6211 : Nat.Prime 6211 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨6211, 2, [(2, 1), (3, 3), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_6353 : Nat.Prime 6353 := by
  apply nodeValid_prime [2, 397] ⟨6353, 3, [(2, 4), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_397
  · decide +kernel

theorem prime_6971 : Nat.Prime 6971 := by
  apply nodeValid_prime [2, 5, 17, 41] ⟨6971, 2, [(2, 1), (5, 1), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_7307 : Nat.Prime 7307 := by
  apply nodeValid_prime [2, 13, 281] ⟨7307, 2, [(2, 1), (13, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_281
  · decide +kernel

theorem prime_9227 : Nat.Prime 9227 := by
  apply nodeValid_prime [2, 7, 659] ⟨9227, 2, [(2, 1), (7, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_659
  · decide +kernel

theorem prime_9781 : Nat.Prime 9781 := by
  apply nodeValid_prime [2, 3, 5, 163] ⟨9781, 6, [(2, 2), (3, 1), (5, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_163
  · decide +kernel

theorem prime_10457 : Nat.Prime 10457 := by
  apply nodeValid_prime [2, 1307] ⟨10457, 3, [(2, 3), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1307
  · decide +kernel

theorem prime_10639 : Nat.Prime 10639 := by
  apply nodeValid_prime [2, 3, 197] ⟨10639, 6, [(2, 1), (3, 3), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
  · decide +kernel

theorem prime_10667 : Nat.Prime 10667 := by
  apply nodeValid_prime [2, 5333] ⟨10667, 2, [(2, 1), (5333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5333
  · decide +kernel

theorem prime_10853 : Nat.Prime 10853 := by
  apply nodeValid_prime [2, 2713] ⟨10853, 2, [(2, 2), (2713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2713
  · decide +kernel

theorem prime_11317 : Nat.Prime 11317 := by
  apply nodeValid_prime [2, 3, 23, 41] ⟨11317, 2, [(2, 2), (3, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_13877 : Nat.Prime 13877 := by
  apply nodeValid_prime [2, 3469] ⟨13877, 2, [(2, 2), (3469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3469
  · decide +kernel

theorem prime_14797 : Nat.Prime 14797 := by
  apply nodeValid_prime [2, 3, 137] ⟨14797, 2, [(2, 2), (3, 3), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_16001 : Nat.Prime 16001 := by
  apply nodeValid_prime [2, 5] ⟨16001, 3, [(2, 7), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_20903 : Nat.Prime 20903 := by
  apply nodeValid_prime [2, 7, 1493] ⟨20903, 5, [(2, 1), (7, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1493
  · decide +kernel

theorem prime_27961 : Nat.Prime 27961 := by
  apply nodeValid_prime [2, 3, 5, 233] ⟨27961, 13, [(2, 3), (3, 1), (5, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233
  · decide +kernel

theorem prime_29851 : Nat.Prime 29851 := by
  apply nodeValid_prime [2, 3, 5, 199] ⟨29851, 2, [(2, 1), (3, 1), (5, 2), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
  · decide +kernel

theorem prime_30113 : Nat.Prime 30113 := by
  apply nodeValid_prime [2, 941] ⟨30113, 3, [(2, 5), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_941
  · decide +kernel

theorem prime_31181 : Nat.Prime 31181 := by
  apply nodeValid_prime [2, 5, 1559] ⟨31181, 2, [(2, 2), (5, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1559
  · decide +kernel

theorem prime_41357 : Nat.Prime 41357 := by
  apply nodeValid_prime [2, 7, 211] ⟨41357, 2, [(2, 2), (7, 2), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
  · decide +kernel

theorem prime_42433 : Nat.Prime 42433 := by
  apply nodeValid_prime [2, 3, 13, 17] ⟨42433, 10, [(2, 6), (3, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_43781 : Nat.Prime 43781 := by
  apply nodeValid_prime [2, 5, 11, 199] ⟨43781, 2, [(2, 2), (5, 1), (11, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_199
  · decide +kernel

theorem prime_46271 : Nat.Prime 46271 := by
  apply nodeValid_prime [2, 5, 7, 661] ⟨46271, 7, [(2, 1), (5, 1), (7, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_661
  · decide +kernel

theorem prime_48463 : Nat.Prime 48463 := by
  apply nodeValid_prime [2, 3, 41, 197] ⟨48463, 5, [(2, 1), (3, 1), (41, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_197
  · decide +kernel

theorem prime_53309 : Nat.Prime 53309 := by
  apply nodeValid_prime [2, 13327] ⟨53309, 2, [(2, 2), (13327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13327
  · decide +kernel

theorem prime_64033 : Nat.Prime 64033 := by
  apply nodeValid_prime [2, 3, 23, 29] ⟨64033, 5, [(2, 5), (3, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_67579 : Nat.Prime 67579 := by
  apply nodeValid_prime [2, 3, 7, 1609] ⟨67579, 7, [(2, 1), (3, 1), (7, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1609
  · decide +kernel

theorem prime_68239 : Nat.Prime 68239 := by
  apply nodeValid_prime [2, 3, 17, 223] ⟨68239, 3, [(2, 1), (3, 2), (17, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_223
  · decide +kernel

theorem prime_81023 : Nat.Prime 81023 := by
  apply nodeValid_prime [2, 17, 2383] ⟨81023, 5, [(2, 1), (17, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2383
  · decide +kernel

theorem prime_87433 : Nat.Prime 87433 := by
  apply nodeValid_prime [2, 3, 3643] ⟨87433, 5, [(2, 3), (3, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3643
  · decide +kernel

theorem prime_87743 : Nat.Prime 87743 := by
  apply nodeValid_prime [2, 19, 2309] ⟨87743, 5, [(2, 1), (19, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2309
  · decide +kernel

theorem prime_91781 : Nat.Prime 91781 := by
  apply nodeValid_prime [2, 5, 13, 353] ⟨91781, 2, [(2, 2), (5, 1), (13, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_353
  · decide +kernel

theorem prime_98011 : Nat.Prime 98011 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨98011, 10, [(2, 1), (3, 4), (5, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_98627 : Nat.Prime 98627 := by
  apply nodeValid_prime [2, 11, 4483] ⟨98627, 2, [(2, 1), (11, 1), (4483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4483
  · decide +kernel

theorem prime_100799 : Nat.Prime 100799 := by
  apply nodeValid_prime [2, 101, 499] ⟨100799, 17, [(2, 1), (101, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_499
  · decide +kernel

theorem prime_105613 : Nat.Prime 105613 := by
  apply nodeValid_prime [2, 3, 13, 677] ⟨105613, 2, [(2, 2), (3, 1), (13, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_677
  · decide +kernel

theorem prime_106961 : Nat.Prime 106961 := by
  apply nodeValid_prime [2, 5, 7, 191] ⟨106961, 3, [(2, 4), (5, 1), (7, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_191
  · decide +kernel

theorem prime_143527 : Nat.Prime 143527 := by
  apply nodeValid_prime [2, 3, 19, 1259] ⟨143527, 3, [(2, 1), (3, 1), (19, 1), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1259
  · decide +kernel

theorem prime_162823 : Nat.Prime 162823 := by
  apply nodeValid_prime [2, 3, 11, 2467] ⟨162823, 3, [(2, 1), (3, 1), (11, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2467
  · decide +kernel

theorem prime_173647 : Nat.Prime 173647 := by
  apply nodeValid_prime [2, 3, 11, 877] ⟨173647, 3, [(2, 1), (3, 2), (11, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_877
  · decide +kernel

theorem prime_185167 : Nat.Prime 185167 := by
  apply nodeValid_prime [2, 3, 127] ⟨185167, 5, [(2, 1), (3, 6), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
  · decide +kernel

theorem prime_215183 : Nat.Prime 215183 := by
  apply nodeValid_prime [2, 11, 9781] ⟨215183, 5, [(2, 1), (11, 1), (9781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_9781
  · decide +kernel

theorem prime_215309 : Nat.Prime 215309 := by
  apply nodeValid_prime [2, 19, 2833] ⟨215309, 2, [(2, 2), (19, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2833
  · decide +kernel

theorem prime_262253 : Nat.Prime 262253 := by
  apply nodeValid_prime [2, 65563] ⟨262253, 2, [(2, 2), (65563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_65563
  · decide +kernel

theorem prime_263257 : Nat.Prime 263257 := by
  apply nodeValid_prime [2, 3, 7, 1567] ⟨263257, 5, [(2, 3), (3, 1), (7, 1), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1567
  · decide +kernel

theorem prime_282679 : Nat.Prime 282679 := by
  apply nodeValid_prime [2, 3, 11, 4283] ⟨282679, 6, [(2, 1), (3, 1), (11, 1), (4283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4283
  · decide +kernel

theorem prime_319391 : Nat.Prime 319391 := by
  apply nodeValid_prime [2, 5, 19, 41] ⟨319391, 13, [(2, 1), (5, 1), (19, 1), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_349829 : Nat.Prime 349829 := by
  apply nodeValid_prime [2, 19, 4603] ⟨349829, 2, [(2, 2), (19, 1), (4603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4603
  · decide +kernel

theorem prime_386039 : Nat.Prime 386039 := by
  apply nodeValid_prime [2, 251, 769] ⟨386039, 11, [(2, 1), (251, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_769
  · decide +kernel

theorem prime_548623 : Nat.Prime 548623 := by
  apply nodeValid_prime [2, 3, 29, 1051] ⟨548623, 3, [(2, 1), (3, 2), (29, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1051
  · decide +kernel

theorem prime_560297 : Nat.Prime 560297 := by
  apply nodeValid_prime [2, 11, 6367] ⟨560297, 3, [(2, 3), (11, 1), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6367
  · decide +kernel

theorem prime_564679 : Nat.Prime 564679 := by
  apply nodeValid_prime [2, 3, 10457] ⟨564679, 3, [(2, 1), (3, 3), (10457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10457
  · decide +kernel

theorem prime_574109 : Nat.Prime 574109 := by
  apply nodeValid_prime [2, 143527] ⟨574109, 2, [(2, 2), (143527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_143527
  · decide +kernel

theorem prime_917363 : Nat.Prime 917363 := by
  apply nodeValid_prime [2, 43, 10667] ⟨917363, 2, [(2, 1), (43, 1), (10667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_10667
  · decide +kernel

theorem prime_1117729 : Nat.Prime 1117729 := by
  apply nodeValid_prime [2, 3, 3881] ⟨1117729, 22, [(2, 5), (3, 2), (3881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3881
  · decide +kernel

theorem prime_1126627 : Nat.Prime 1126627 := by
  apply nodeValid_prime [2, 3, 179, 1049] ⟨1126627, 2, [(2, 1), (3, 1), (179, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_1049
  · decide +kernel

theorem prime_1306891 : Nat.Prime 1306891 := by
  apply nodeValid_prime [2, 3, 5, 13, 1117] ⟨1306891, 2, [(2, 1), (3, 2), (5, 1), (13, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1117
  · decide +kernel

theorem prime_1343863 : Nat.Prime 1343863 := by
  apply nodeValid_prime [2, 3, 13, 5743] ⟨1343863, 3, [(2, 1), (3, 2), (13, 1), (5743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5743
  · decide +kernel

theorem prime_1383757 : Nat.Prime 1383757 := by
  apply nodeValid_prime [2, 3, 11, 953] ⟨1383757, 2, [(2, 2), (3, 1), (11, 2), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_953
  · decide +kernel

theorem prime_2422099 : Nat.Prime 2422099 := by
  apply nodeValid_prime [2, 3, 7, 47, 409] ⟨2422099, 3, [(2, 1), (3, 2), (7, 1), (47, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_409
  · decide +kernel

theorem prime_2801003 : Nat.Prime 2801003 := by
  apply nodeValid_prime [2, 67, 20903] ⟨2801003, 2, [(2, 1), (67, 1), (20903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_20903
  · decide +kernel

theorem prime_3422753 : Nat.Prime 3422753 := by
  apply nodeValid_prime [2, 106961] ⟨3422753, 3, [(2, 5), (106961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_106961
  · decide +kernel

theorem prime_3934033 : Nat.Prime 3934033 := by
  apply nodeValid_prime [2, 3, 41, 1999] ⟨3934033, 7, [(2, 4), (3, 1), (41, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1999
  · decide +kernel

theorem prime_3986737 : Nat.Prime 3986737 := by
  apply nodeValid_prime [2, 3, 13, 6389] ⟨3986737, 7, [(2, 4), (3, 1), (13, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6389
  · decide +kernel

theorem prime_6067073 : Nat.Prime 6067073 := by
  apply nodeValid_prime [2, 11, 31, 139] ⟨6067073, 3, [(2, 7), (11, 1), (31, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_139
  · decide +kernel

theorem prime_9161143 : Nat.Prime 9161143 := by
  apply nodeValid_prime [2, 3, 877, 1741] ⟨9161143, 3, [(2, 1), (3, 1), (877, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_877
    · exact prime_1741
  · decide +kernel

theorem prime_9362321 : Nat.Prime 9362321 := by
  apply nodeValid_prime [2, 5, 11, 10639] ⟨9362321, 3, [(2, 4), (5, 1), (11, 1), (10639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_10639
  · decide +kernel

theorem prime_9552457 : Nat.Prime 9552457 := by
  apply nodeValid_prime [2, 3, 181, 733] ⟨9552457, 10, [(2, 3), (3, 2), (181, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_733
  · decide +kernel

theorem prime_13679833 : Nat.Prime 13679833 := by
  apply nodeValid_prime [2, 3, 17, 33529] ⟨13679833, 5, [(2, 3), (3, 1), (17, 1), (33529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_33529
  · decide +kernel

theorem prime_20008259 : Nat.Prime 20008259 := by
  apply nodeValid_prime [2, 109, 91781] ⟨20008259, 2, [(2, 1), (109, 1), (91781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_91781
  · decide +kernel

theorem prime_20338523 : Nat.Prime 20338523 := by
  apply nodeValid_prime [2, 937, 10853] ⟨20338523, 2, [(2, 1), (937, 1), (10853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_937
    · exact prime_10853
  · decide +kernel

theorem prime_22140113 : Nat.Prime 22140113 := by
  apply nodeValid_prime [2, 1383757] ⟨22140113, 3, [(2, 4), (1383757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1383757
  · decide +kernel

theorem prime_24075001 : Nat.Prime 24075001 := by
  apply nodeValid_prime [2, 3, 5, 107] ⟨24075001, 7, [(2, 3), (3, 2), (5, 5), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_25664183 : Nat.Prime 25664183 := by
  apply nodeValid_prime [2, 23, 673, 829] ⟨25664183, 5, [(2, 1), (23, 1), (673, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_673
    · exact prime_829
  · decide +kernel

theorem prime_29684279 : Nat.Prime 29684279 := by
  apply nodeValid_prime [2, 13, 17, 239, 281] ⟨29684279, 7, [(2, 1), (13, 1), (17, 1), (239, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_239
    · exact prime_281
  · decide +kernel

theorem prime_30261047 : Nat.Prime 30261047 := by
  apply nodeValid_prime [2, 3061, 4943] ⟨30261047, 5, [(2, 1), (3061, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3061
    · exact prime_4943
  · decide +kernel

theorem prime_31004497 : Nat.Prime 31004497 := by
  apply nodeValid_prime [2, 3, 215309] ⟨31004497, 5, [(2, 4), (3, 2), (215309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_215309
  · decide +kernel

theorem prime_33205751 : Nat.Prime 33205751 := by
  apply nodeValid_prime [2, 5, 317, 419] ⟨33205751, 29, [(2, 1), (5, 3), (317, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_317
    · exact prime_419
  · decide +kernel

theorem prime_34156363 : Nat.Prime 34156363 := by
  apply nodeValid_prime [2, 3, 41, 43, 3229] ⟨34156363, 3, [(2, 1), (3, 1), (41, 1), (43, 1), (3229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_43
    · exact prime_3229
  · decide +kernel

theorem prime_41268377 : Nat.Prime 41268377 := by
  apply nodeValid_prime [2, 59, 87433] ⟨41268377, 3, [(2, 3), (59, 1), (87433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_87433
  · decide +kernel

theorem prime_46618487 : Nat.Prime 46618487 := by
  apply nodeValid_prime [2, 29, 491, 1637] ⟨46618487, 5, [(2, 1), (29, 1), (491, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_491
    · exact prime_1637
  · decide +kernel

theorem prime_49995091 : Nat.Prime 49995091 := by
  apply nodeValid_prime [2, 3, 5, 185167] ⟨49995091, 3, [(2, 1), (3, 3), (5, 1), (185167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_185167
  · decide +kernel

theorem prime_53731591 : Nat.Prime 53731591 := by
  apply nodeValid_prime [2, 3, 5, 11, 162823] ⟨53731591, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (162823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_162823
  · decide +kernel

theorem prime_59010437 : Nat.Prime 59010437 := by
  apply nodeValid_prime [2, 997, 14797] ⟨59010437, 2, [(2, 2), (997, 1), (14797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_997
    · exact prime_14797
  · decide +kernel

theorem prime_62189381 : Nat.Prime 62189381 := by
  apply nodeValid_prime [2, 5, 11, 282679] ⟨62189381, 2, [(2, 2), (5, 1), (11, 1), (282679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_282679
  · decide +kernel

theorem prime_67458791 : Nat.Prime 67458791 := by
  apply nodeValid_prime [2, 5, 7, 31, 4441] ⟨67458791, 7, [(2, 1), (5, 1), (7, 2), (31, 1), (4441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_4441
  · decide +kernel

theorem prime_88860971 : Nat.Prime 88860971 := by
  apply nodeValid_prime [2, 5, 11, 179, 4513] ⟨88860971, 2, [(2, 1), (5, 1), (11, 1), (179, 1), (4513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_179
    · exact prime_4513
  · decide +kernel

theorem prime_94147673 : Nat.Prime 94147673 := by
  apply nodeValid_prime [2, 2137, 5507] ⟨94147673, 3, [(2, 3), (2137, 1), (5507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2137
    · exact prime_5507
  · decide +kernel

theorem prime_111772901 : Nat.Prime 111772901 := by
  apply nodeValid_prime [2, 5, 1117729] ⟨111772901, 2, [(2, 2), (5, 2), (1117729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1117729
  · decide +kernel

theorem prime_134917583 : Nat.Prime 134917583 := by
  apply nodeValid_prime [2, 67458791] ⟨134917583, 5, [(2, 1), (67458791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67458791
  · decide +kernel

theorem prime_149387089 : Nat.Prime 149387089 := by
  apply nodeValid_prime [2, 3, 1543, 2017] ⟨149387089, 13, [(2, 4), (3, 1), (1543, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1543
    · exact prime_2017
  · decide +kernel

theorem prime_150909211 : Nat.Prime 150909211 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 1279] ⟨150909211, 10, [(2, 1), (3, 3), (5, 1), (19, 1), (23, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_1279
  · decide +kernel

theorem prime_252348869 : Nat.Prime 252348869 := by
  apply nodeValid_prime [2, 719, 87743] ⟨252348869, 2, [(2, 2), (719, 1), (87743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_719
    · exact prime_87743
  · decide +kernel

theorem prime_289042163 : Nat.Prime 289042163 := by
  apply nodeValid_prime [2, 3301, 43781] ⟨289042163, 2, [(2, 1), (3301, 1), (43781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3301
    · exact prime_43781
  · decide +kernel

theorem prime_307970197 : Nat.Prime 307970197 := by
  apply nodeValid_prime [2, 3, 25664183] ⟨307970197, 2, [(2, 2), (3, 1), (25664183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25664183
  · decide +kernel

theorem prime_581303761 : Nat.Prime 581303761 := by
  apply nodeValid_prime [2, 3, 5, 2422099] ⟨581303761, 7, [(2, 4), (3, 1), (5, 1), (2422099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2422099
  · decide +kernel

theorem prime_1292183993 : Nat.Prime 1292183993 := by
  apply nodeValid_prime [2, 11, 743, 19763] ⟨1292183993, 3, [(2, 3), (11, 1), (743, 1), (19763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_743
    · exact prime_19763
  · decide +kernel

theorem prime_1353749987 : Nat.Prime 1353749987 := by
  apply nodeValid_prime [2, 29, 89, 262253] ⟨1353749987, 2, [(2, 1), (29, 1), (89, 1), (262253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_89
    · exact prime_262253
  · decide +kernel

theorem prime_3620574479 : Nat.Prime 3620574479 := by
  apply nodeValid_prime [2, 53, 34156363] ⟨3620574479, 7, [(2, 1), (53, 1), (34156363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_34156363
  · decide +kernel

theorem prime_5146746503 : Nat.Prime 5146746503 := by
  apply nodeValid_prime [2, 83, 31004497] ⟨5146746503, 5, [(2, 1), (83, 1), (31004497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_31004497
  · decide +kernel

theorem prime_5666538487 : Nat.Prime 5666538487 := by
  apply nodeValid_prime [2, 3, 7, 134917583] ⟨5666538487, 3, [(2, 1), (3, 1), (7, 1), (134917583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_134917583
  · decide +kernel

theorem prime_16664476391 : Nat.Prime 16664476391 := by
  apply nodeValid_prime [2, 5, 107, 557, 27961] ⟨16664476391, 23, [(2, 1), (5, 1), (107, 1), (557, 1), (27961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_557
    · exact prime_27961
  · decide +kernel

theorem prime_23466131267 : Nat.Prime 23466131267 := by
  apply nodeValid_prime [2, 107, 191, 574109] ⟨23466131267, 2, [(2, 1), (107, 1), (191, 1), (574109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_191
    · exact prime_574109
  · decide +kernel

theorem prime_30786562019 : Nat.Prime 30786562019 := by
  apply nodeValid_prime [2, 61, 252348869] ⟨30786562019, 2, [(2, 1), (61, 1), (252348869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_252348869
  · decide +kernel

theorem prime_33431481799 : Nat.Prime 33431481799 := by
  apply nodeValid_prime [2, 3, 11, 13, 313, 11317] ⟨33431481799, 3, [(2, 1), (3, 1), (11, 2), (13, 1), (313, 1), (11317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_313
    · exact prime_11317
  · decide +kernel

theorem prime_38659389157 : Nat.Prime 38659389157 := by
  apply nodeValid_prime [2, 3, 59, 6067073] ⟨38659389157, 2, [(2, 2), (3, 3), (59, 1), (6067073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_6067073
  · decide +kernel

theorem prime_51154730969 : Nat.Prime 51154730969 := by
  apply nodeValid_prime [2, 11, 581303761] ⟨51154730969, 3, [(2, 3), (11, 1), (581303761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_581303761
  · decide +kernel

theorem prime_74759922101 : Nat.Prime 74759922101 := by
  apply nodeValid_prime [2, 5, 9227, 81023] ⟨74759922101, 3, [(2, 2), (5, 2), (9227, 1), (81023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9227
    · exact prime_81023
  · decide +kernel

theorem prime_75220840361 : Nat.Prime 75220840361 := by
  apply nodeValid_prime [2, 5, 23, 829, 98627] ⟨75220840361, 3, [(2, 3), (5, 1), (23, 1), (829, 1), (98627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_829
    · exact prime_98627
  · decide +kernel

theorem prime_101997692767 : Nat.Prime 101997692767 := by
  apply nodeValid_prime [2, 3, 5666538487] ⟨101997692767, 3, [(2, 1), (3, 2), (5666538487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5666538487
  · decide +kernel

theorem prime_149290015057 : Nat.Prime 149290015057 := by
  apply nodeValid_prime [2, 3, 7, 13, 61, 560297] ⟨149290015057, 5, [(2, 4), (3, 1), (7, 1), (13, 1), (61, 1), (560297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_560297
  · decide +kernel

theorem prime_301808073251 : Nat.Prime 301808073251 := by
  apply nodeValid_prime [2, 5, 431, 2801003] ⟨301808073251, 2, [(2, 1), (5, 3), (431, 1), (2801003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_431
    · exact prime_2801003
  · decide +kernel

theorem prime_306460496201 : Nat.Prime 306460496201 := by
  apply nodeValid_prime [2, 5, 19, 23, 503, 6971] ⟨306460496201, 6, [(2, 3), (5, 2), (19, 1), (23, 1), (503, 1), (6971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_503
    · exact prime_6971
  · decide +kernel

theorem prime_307396761401 : Nat.Prime 307396761401 := by
  apply nodeValid_prime [2, 5, 59, 563, 46271] ⟨307396761401, 3, [(2, 3), (5, 2), (59, 1), (563, 1), (46271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_563
    · exact prime_46271
  · decide +kernel

theorem prime_308334950999 : Nat.Prime 308334950999 := by
  apply nodeValid_prime [2, 37, 67, 62189381] ⟨308334950999, 11, [(2, 1), (37, 1), (67, 1), (62189381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_67
    · exact prime_62189381
  · decide +kernel

theorem prime_309275114411 : Nat.Prime 309275114411 := by
  apply nodeValid_prime [2, 5, 107, 289042163] ⟨309275114411, 2, [(2, 1), (5, 1), (107, 1), (289042163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_289042163
  · decide +kernel

theorem prime_596241455267 : Nat.Prime 596241455267 := by
  apply nodeValid_prime [2, 67, 89, 49995091] ⟨596241455267, 2, [(2, 1), (67, 1), (89, 1), (49995091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_89
    · exact prime_49995091
  · decide +kernel

theorem prime_596241455449 : Nat.Prime 596241455449 := by
  apply nodeValid_prime [2, 3, 421, 59010437] ⟨596241455449, 7, [(2, 3), (3, 1), (421, 1), (59010437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
    · exact prime_59010437
  · decide +kernel

theorem prime_596241474767 : Nat.Prime 596241474767 := by
  apply nodeValid_prime [2, 7, 29, 61, 24075001] ⟨596241474767, 5, [(2, 1), (7, 1), (29, 1), (61, 1), (24075001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_61
    · exact prime_24075001
  · decide +kernel

theorem prime_597159945313 : Nat.Prime 597159945313 := by
  apply nodeValid_prime [2, 3, 7, 97, 9161143] ⟨597159945313, 5, [(2, 5), (3, 1), (7, 1), (97, 1), (9161143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_9161143
  · decide +kernel

theorem prime_597160059581 : Nat.Prime 597160059581 := by
  apply nodeValid_prime [2, 5, 7, 19, 167, 431, 3119] ⟨597160059581, 2, [(2, 2), (5, 1), (7, 1), (19, 1), (167, 1), (431, 1), (3119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_167
    · exact prime_431
    · exact prime_3119
  · decide +kernel

theorem prime_597160060229 : Nat.Prime 597160060229 := by
  apply nodeValid_prime [2, 149290015057] ⟨597160060229, 2, [(2, 2), (149290015057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_149290015057
  · decide +kernel

theorem prime_598079332771 : Nat.Prime 598079332771 := by
  apply nodeValid_prime [2, 3, 5, 2087, 9552457] ⟨598079332771, 2, [(2, 1), (3, 1), (5, 1), (2087, 1), (9552457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2087
    · exact prime_9552457
  · decide +kernel

theorem prime_598079332909 : Nat.Prime 598079332909 := by
  apply nodeValid_prime [2, 3, 61, 30261047] ⟨598079332909, 10, [(2, 2), (3, 4), (61, 1), (30261047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_30261047
  · decide +kernel

theorem prime_598079376809 : Nat.Prime 598079376809 := by
  apply nodeValid_prime [2, 74759922101] ⟨598079376809, 3, [(2, 3), (74759922101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_74759922101
  · decide +kernel

theorem prime_598999758353 : Nat.Prime 598999758353 := by
  apply nodeValid_prime [2, 68239, 548623] ⟨598999758353, 3, [(2, 4), (68239, 1), (548623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_68239
    · exact prime_548623
  · decide +kernel

theorem prime_598999758479 : Nat.Prime 598999758479 := by
  apply nodeValid_prime [2, 11, 101, 6353, 42433] ⟨598999758479, 11, [(2, 1), (11, 1), (101, 1), (6353, 1), (42433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_101
    · exact prime_6353
    · exact prime_42433
  · decide +kernel

theorem prime_598999776469 : Nat.Prime 598999776469 := by
  apply nodeValid_prime [2, 3, 929, 53731591] ⟨598999776469, 6, [(2, 2), (3, 1), (929, 1), (53731591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
    · exact prime_53731591
  · decide +kernel

theorem prime_599921138657 : Nat.Prime 599921138657 := by
  apply nodeValid_prime [2, 7, 79, 349, 13877] ⟨599921138657, 3, [(2, 5), (7, 2), (79, 1), (349, 1), (13877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_349
    · exact prime_13877
  · decide +kernel

theorem prime_599921150077 : Nat.Prime 599921150077 := by
  apply nodeValid_prime [2, 3, 16664476391] ⟨599921150077, 2, [(2, 2), (3, 2), (16664476391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16664476391
  · decide +kernel

theorem prime_599921150207 : Nat.Prime 599921150207 := by
  apply nodeValid_prime [2, 7, 29, 67, 193, 229, 499] ⟨599921150207, 5, [(2, 1), (7, 1), (29, 1), (67, 1), (193, 1), (229, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_67
    · exact prime_193
    · exact prime_229
    · exact prime_499
  · decide +kernel

theorem prime_600843452849 : Nat.Prime 600843452849 := by
  apply nodeValid_prime [2, 89, 1093, 386039] ⟨600843452849, 3, [(2, 4), (89, 1), (1093, 1), (386039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1093
    · exact prime_386039
  · decide +kernel

theorem prime_600843459457 : Nat.Prime 600843459457 := by
  apply nodeValid_prime [2, 3, 23, 71, 319391] ⟨600843459457, 5, [(2, 7), (3, 2), (23, 1), (71, 1), (319391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_71
    · exact prime_319391
  · decide +kernel

theorem prime_600843459757 : Nat.Prime 600843459757 := by
  apply nodeValid_prime [2, 3, 53, 347, 1571, 1733] ⟨600843459757, 2, [(2, 2), (3, 1), (53, 1), (347, 1), (1571, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_347
    · exact prime_1571
    · exact prime_1733
  · decide +kernel

theorem prime_601766671427 : Nat.Prime 601766671427 := by
  apply nodeValid_prime [2, 907, 10639, 31181] ⟨601766671427, 2, [(2, 1), (907, 1), (10639, 1), (31181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_907
    · exact prime_10639
    · exact prime_31181
  · decide +kernel

theorem prime_601766672383 : Nat.Prime 601766672383 := by
  apply nodeValid_prime [2, 3, 33431481799] ⟨601766672383, 5, [(2, 1), (3, 2), (33431481799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33431481799
  · decide +kernel

theorem prime_601766722889 : Nat.Prime 601766722889 := by
  apply nodeValid_prime [2, 75220840361] ⟨601766722889, 3, [(2, 3), (75220840361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_75220840361
  · decide +kernel

theorem prime_602690951449 : Nat.Prime 602690951449 := by
  apply nodeValid_prime [2, 3, 19, 59, 1933, 3863] ⟨602690951449, 13, [(2, 3), (3, 2), (19, 1), (59, 1), (1933, 1), (3863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
    · exact prime_1933
    · exact prime_3863
  · decide +kernel

theorem prime_602690978467 : Nat.Prime 602690978467 := by
  apply nodeValid_prime [2, 3, 17, 19, 113, 917363] ⟨602690978467, 2, [(2, 1), (3, 2), (17, 1), (19, 1), (113, 1), (917363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_113
    · exact prime_917363
  · decide +kernel

theorem prime_602690979239 : Nat.Prime 602690979239 := by
  apply nodeValid_prime [2, 131, 577, 3986737] ⟨602690979239, 13, [(2, 1), (131, 1), (577, 1), (3986737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_577
    · exact prime_3986737
  · decide +kernel

theorem prime_603616146503 : Nat.Prime 603616146503 := by
  apply nodeValid_prime [2, 301808073251] ⟨603616146503, 5, [(2, 1), (301808073251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_301808073251
  · decide +kernel

theorem prime_603616169069 : Nat.Prime 603616169069 := by
  apply nodeValid_prime [2, 11, 103, 4423, 30113] ⟨603616169069, 2, [(2, 2), (11, 1), (103, 1), (4423, 1), (30113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_103
    · exact prime_4423
    · exact prime_30113
  · decide +kernel

theorem prime_603616169677 : Nat.Prime 603616169677 := by
  apply nodeValid_prime [2, 3, 13, 83, 46618487] ⟨603616169677, 5, [(2, 2), (3, 1), (13, 1), (83, 1), (46618487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
    · exact prime_46618487
  · decide +kernel

theorem prime_604542291679 : Nat.Prime 604542291679 := by
  apply nodeValid_prime [2, 3, 13, 48463, 53309] ⟨604542291679, 6, [(2, 1), (3, 2), (13, 1), (48463, 1), (53309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_48463
    · exact prime_53309
  · decide +kernel

theorem prime_604542293533 : Nat.Prime 604542293533 := by
  apply nodeValid_prime [2, 3, 16001, 349829] ⟨604542293533, 5, [(2, 2), (3, 3), (16001, 1), (349829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16001
    · exact prime_349829
  · decide +kernel

theorem prime_604542299267 : Nat.Prime 604542299267 := by
  apply nodeValid_prime [2, 2003, 150909211] ⟨604542299267, 2, [(2, 1), (2003, 1), (150909211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2003
    · exact prime_150909211
  · decide +kernel

theorem prime_605469407303 : Nat.Prime 605469407303 := by
  apply nodeValid_prime [2, 983, 307970197] ⟨605469407303, 5, [(2, 1), (983, 1), (307970197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_983
    · exact prime_307970197
  · decide +kernel

theorem prime_605469408581 : Nat.Prime 605469408581 := by
  apply nodeValid_prime [2, 5, 2213, 13679833] ⟨605469408581, 2, [(2, 2), (5, 1), (2213, 1), (13679833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2213
    · exact prime_13679833
  · decide +kernel

theorem prime_605469411473 : Nat.Prime 605469411473 := by
  apply nodeValid_prime [2, 29, 971, 1343863] ⟨605469411473, 3, [(2, 4), (29, 1), (971, 1), (1343863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_971
    · exact prime_1343863
  · decide +kernel

theorem prime_606397484521 : Nat.Prime 606397484521 := by
  apply nodeValid_prime [2, 3, 5, 19, 157, 564679] ⟨606397484521, 7, [(2, 3), (3, 2), (5, 1), (19, 1), (157, 1), (564679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_157
    · exact prime_564679
  · decide +kernel

theorem prime_606397531171 : Nat.Prime 606397531171 := by
  apply nodeValid_prime [2, 3, 5, 17, 127, 9362321] ⟨606397531171, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (127, 1), (9362321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_127
    · exact prime_9362321
  · decide +kernel

theorem prime_606397531639 : Nat.Prime 606397531639 := by
  apply nodeValid_prime [2, 3, 31, 79, 41268377] ⟨606397531639, 17, [(2, 1), (3, 1), (31, 1), (79, 1), (41268377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_79
    · exact prime_41268377
  · decide +kernel

theorem prime_607326474077 : Nat.Prime 607326474077 := by
  apply nodeValid_prime [2, 7, 100799, 215183] ⟨607326474077, 2, [(2, 2), (7, 1), (100799, 1), (215183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_100799
    · exact prime_215183
  · decide +kernel

theorem prime_607326476711 : Nat.Prime 607326476711 := by
  apply nodeValid_prime [2, 5, 47, 1292183993] ⟨607326476711, 11, [(2, 1), (5, 1), (47, 1), (1292183993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_1292183993
  · decide +kernel

theorem prime_607326526049 : Nat.Prime 607326526049 := by
  apply nodeValid_prime [2, 11, 211, 67579] ⟨607326526049, 3, [(2, 5), (11, 3), (211, 1), (67579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_211
    · exact prime_67579
  · decide +kernel

theorem prime_608256512473 : Nat.Prime 608256512473 := by
  apply nodeValid_prime [2, 3, 7, 3620574479] ⟨608256512473, 5, [(2, 3), (3, 1), (7, 1), (3620574479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3620574479
  · decide +kernel

theorem prime_608256513421 : Nat.Prime 608256513421 := by
  apply nodeValid_prime [2, 3, 5, 229, 1483, 29851] ⟨608256513421, 10, [(2, 2), (3, 1), (5, 1), (229, 1), (1483, 1), (29851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
    · exact prime_1483
    · exact prime_29851
  · decide +kernel

theorem prime_608256530383 : Nat.Prime 608256530383 := by
  apply nodeValid_prime [2, 3, 37, 47, 89, 271, 2417] ⟨608256530383, 5, [(2, 1), (3, 1), (37, 1), (47, 1), (89, 1), (271, 1), (2417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_47
    · exact prime_89
    · exact prime_271
    · exact prime_2417
  · decide +kernel

theorem prime_609187494151 : Nat.Prime 609187494151 := by
  apply nodeValid_prime [2, 3, 5, 1353749987] ⟨609187494151, 3, [(2, 1), (3, 2), (5, 2), (1353749987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1353749987
  · decide +kernel

theorem prime_609187498187 : Nat.Prime 609187498187 := by
  apply nodeValid_prime [2, 37, 7307, 1126627] ⟨609187498187, 2, [(2, 1), (37, 1), (7307, 1), (1126627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_7307
    · exact prime_1126627
  · decide +kernel

theorem prime_610119412943 : Nat.Prime 610119412943 := by
  apply nodeValid_prime [2, 13, 23466131267] ⟨610119412943, 5, [(2, 1), (13, 1), (23466131267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23466131267
  · decide +kernel

theorem prime_610119413263 : Nat.Prime 610119413263 := by
  apply nodeValid_prime [2, 3, 3301, 3422753] ⟨610119413263, 3, [(2, 1), (3, 3), (3301, 1), (3422753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3301
    · exact prime_3422753
  · decide +kernel

theorem prime_610119426887 : Nat.Prime 610119426887 := by
  apply nodeValid_prime [2, 3433, 88860971] ⟨610119426887, 5, [(2, 1), (3433, 1), (88860971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3433
    · exact prime_88860971
  · decide +kernel

theorem prime_611052229861 : Nat.Prime 611052229861 := by
  apply nodeValid_prime [2, 3, 5, 509, 20008259] ⟨611052229861, 6, [(2, 2), (3, 1), (5, 1), (509, 1), (20008259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_509
    · exact prime_20008259
  · decide +kernel

theorem prime_611052229903 : Nat.Prime 611052229903 := by
  apply nodeValid_prime [2, 3, 3067, 33205751] ⟨611052229903, 3, [(2, 1), (3, 1), (3067, 1), (33205751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3067
    · exact prime_33205751
  · decide +kernel

theorem prime_611052323809 : Nat.Prime 611052323809 := by
  apply nodeValid_prime [2, 3, 101, 643, 98011] ⟨611052323809, 19, [(2, 5), (3, 1), (101, 1), (643, 1), (98011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_643
    · exact prime_98011
  · decide +kernel

theorem prime_611986156603 : Nat.Prime 611986156603 := by
  apply nodeValid_prime [2, 3, 101997692767] ⟨611986156603, 2, [(2, 1), (3, 1), (101997692767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101997692767
  · decide +kernel

theorem prime_611986157071 : Nat.Prime 611986157071 := by
  apply nodeValid_prime [2, 3, 5, 17, 59, 20338523] ⟨611986157071, 6, [(2, 1), (3, 1), (5, 1), (17, 1), (59, 1), (20338523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_59
    · exact prime_20338523
  · decide +kernel

theorem prime_611986176749 : Nat.Prime 611986176749 := by
  apply nodeValid_prime [2, 29, 47, 1753, 64033] ⟨611986176749, 2, [(2, 2), (29, 1), (47, 1), (1753, 1), (64033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_47
    · exact prime_1753
    · exact prime_64033
  · decide +kernel

theorem prime_612920991673 : Nat.Prime 612920991673 := by
  apply nodeValid_prime [2, 3, 11, 491, 1153, 1367] ⟨612920991673, 5, [(2, 3), (3, 2), (11, 1), (491, 1), (1153, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_491
    · exact prime_1153
    · exact prime_1367
  · decide +kernel

theorem prime_612920992403 : Nat.Prime 612920992403 := by
  apply nodeValid_prime [2, 306460496201] ⟨612920992403, 2, [(2, 1), (306460496201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_306460496201
  · decide +kernel

theorem prime_612920992793 : Nat.Prime 612920992793 := by
  apply nodeValid_prime [2, 29, 89, 29684279] ⟨612920992793, 3, [(2, 3), (29, 1), (89, 1), (29684279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_89
    · exact prime_29684279
  · decide +kernel

theorem prime_613856771629 : Nat.Prime 613856771629 := by
  apply nodeValid_prime [2, 3, 51154730969] ⟨613856771629, 2, [(2, 2), (3, 1), (51154730969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51154730969
  · decide +kernel

theorem prime_613856772293 : Nat.Prime 613856772293 := by
  apply nodeValid_prime [2, 1373, 111772901] ⟨613856772293, 2, [(2, 2), (1373, 1), (111772901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1373
    · exact prime_111772901
  · decide +kernel

theorem prime_613856773039 : Nat.Prime 613856773039 := by
  apply nodeValid_prime [2, 3, 4621, 22140113] ⟨613856773039, 3, [(2, 1), (3, 1), (4621, 1), (22140113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4621
    · exact prime_22140113
  · decide +kernel

theorem prime_614793522803 : Nat.Prime 614793522803 := by
  apply nodeValid_prime [2, 307396761401] ⟨614793522803, 2, [(2, 1), (307396761401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_307396761401
  · decide +kernel

theorem prime_614793549353 : Nat.Prime 614793549353 := by
  apply nodeValid_prime [2, 47, 6211, 263257] ⟨614793549353, 3, [(2, 3), (47, 1), (6211, 1), (263257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_6211
    · exact prime_263257
  · decide +kernel

theorem prime_614793550697 : Nat.Prime 614793550697 := by
  apply nodeValid_prime [2, 13, 223, 251, 105613] ⟨614793550697, 3, [(2, 3), (13, 1), (223, 1), (251, 1), (105613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_223
    · exact prime_251
    · exact prime_105613
  · decide +kernel

theorem prime_615731239523 : Nat.Prime 615731239523 := by
  apply nodeValid_prime [2, 7, 73, 461, 1306891] ⟨615731239523, 2, [(2, 1), (7, 1), (73, 1), (461, 1), (1306891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_461
    · exact prime_1306891
  · decide +kernel

theorem prime_615731240381 : Nat.Prime 615731240381 := by
  apply nodeValid_prime [2, 5, 30786562019] ⟨615731240381, 2, [(2, 2), (5, 1), (30786562019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30786562019
  · decide +kernel

theorem prime_615731240963 : Nat.Prime 615731240963 := by
  apply nodeValid_prime [2, 139, 563, 3934033] ⟨615731240963, 2, [(2, 1), (139, 1), (563, 1), (3934033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_563
    · exact prime_3934033
  · decide +kernel

theorem prime_616669901999 : Nat.Prime 616669901999 := by
  apply nodeValid_prime [2, 308334950999] ⟨616669901999, 7, [(2, 1), (308334950999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_308334950999
  · decide +kernel

theorem prime_616669903393 : Nat.Prime 616669903393 := by
  apply nodeValid_prime [2, 3, 43, 149387089] ⟨616669903393, 5, [(2, 5), (3, 1), (43, 1), (149387089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_149387089
  · decide +kernel

theorem prime_616669925873 : Nat.Prime 616669925873 := by
  apply nodeValid_prime [2, 7, 11, 13, 19, 41357] ⟨616669925873, 5, [(2, 4), (7, 3), (11, 1), (13, 1), (19, 1), (41357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_41357
  · decide +kernel

theorem prime_617609580361 : Nat.Prime 617609580361 := by
  apply nodeValid_prime [2, 3, 5, 5146746503] ⟨617609580361, 13, [(2, 3), (3, 1), (5, 1), (5146746503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5146746503
  · decide +kernel

theorem prime_617609590313 : Nat.Prime 617609590313 := by
  apply nodeValid_prime [2, 11, 13, 3109, 173647] ⟨617609590313, 3, [(2, 3), (11, 1), (13, 1), (3109, 1), (173647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_3109
    · exact prime_173647
  · decide +kernel

theorem prime_617609590523 : Nat.Prime 617609590523 := by
  apply nodeValid_prime [2, 79, 1151, 1447, 2347] ⟨617609590523, 2, [(2, 1), (79, 1), (1151, 1), (1447, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1151
    · exact prime_1447
    · exact prime_2347
  · decide +kernel

theorem prime_618550211611 : Nat.Prime 618550211611 := by
  apply nodeValid_prime [2, 3, 5, 73, 94147673] ⟨618550211611, 10, [(2, 1), (3, 2), (5, 1), (73, 1), (94147673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_94147673
  · decide +kernel

theorem prime_618550226513 : Nat.Prime 618550226513 := by
  apply nodeValid_prime [2, 38659389157] ⟨618550226513, 3, [(2, 4), (38659389157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38659389157
  · decide +kernel

theorem prime_618550228823 : Nat.Prime 618550228823 := by
  apply nodeValid_prime [2, 309275114411] ⟨618550228823, 5, [(2, 1), (309275114411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_309275114411
  · decide +kernel

end Sude.Lucas.Generated
