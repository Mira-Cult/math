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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0110
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0121
import Sude.GeneratedFTT.N0125
import Sude.GeneratedFTT.N0141

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7459 : Nat.Prime 7459 := by
  apply nodeValid_prime [2, 3, 11, 113] ⟨7459, 2, [(2, 1), (3, 1), (11, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
  · decide +kernel

theorem prime_13679 : Nat.Prime 13679 := by
  apply nodeValid_prime [2, 7, 977] ⟨13679, 7, [(2, 1), (7, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_977
  · decide +kernel

theorem prime_15101 : Nat.Prime 15101 := by
  apply nodeValid_prime [2, 5, 151] ⟨15101, 2, [(2, 2), (5, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
  · decide +kernel

theorem prime_15233 : Nat.Prime 15233 := by
  apply nodeValid_prime [2, 7, 17] ⟨15233, 3, [(2, 7), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_15581 : Nat.Prime 15581 := by
  apply nodeValid_prime [2, 5, 19, 41] ⟨15581, 2, [(2, 2), (5, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_19867 : Nat.Prime 19867 := by
  apply nodeValid_prime [2, 3, 7, 11, 43] ⟨19867, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_19919 : Nat.Prime 19919 := by
  apply nodeValid_prime [2, 23, 433] ⟨19919, 7, [(2, 1), (23, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_433
  · decide +kernel

theorem prime_20183 : Nat.Prime 20183 := by
  apply nodeValid_prime [2, 10091] ⟨20183, 5, [(2, 1), (10091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10091
  · decide +kernel

theorem prime_20641 : Nat.Prime 20641 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨20641, 7, [(2, 5), (3, 1), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_36947 : Nat.Prime 36947 := by
  apply nodeValid_prime [2, 7, 13, 29] ⟨36947, 2, [(2, 1), (7, 2), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_38861 : Nat.Prime 38861 := by
  apply nodeValid_prime [2, 5, 29, 67] ⟨38861, 14, [(2, 2), (5, 1), (29, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_67
  · decide +kernel

theorem prime_40129 : Nat.Prime 40129 := by
  apply nodeValid_prime [2, 3, 11, 19] ⟨40129, 7, [(2, 6), (3, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_42773 : Nat.Prime 42773 := by
  apply nodeValid_prime [2, 17, 37] ⟨42773, 3, [(2, 2), (17, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_45491 : Nat.Prime 45491 := by
  apply nodeValid_prime [2, 5, 4549] ⟨45491, 2, [(2, 1), (5, 1), (4549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4549
  · decide +kernel

theorem prime_52859 : Nat.Prime 52859 := by
  apply nodeValid_prime [2, 13, 19, 107] ⟨52859, 6, [(2, 1), (13, 1), (19, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_107
  · decide +kernel

theorem prime_64283 : Nat.Prime 64283 := by
  apply nodeValid_prime [2, 32141] ⟨64283, 2, [(2, 1), (32141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32141
  · decide +kernel

theorem prime_70009 : Nat.Prime 70009 := by
  apply nodeValid_prime [2, 3, 2917] ⟨70009, 19, [(2, 3), (3, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2917
  · decide +kernel

theorem prime_72077 : Nat.Prime 72077 := by
  apply nodeValid_prime [2, 37, 487] ⟨72077, 2, [(2, 2), (37, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_487
  · decide +kernel

theorem prime_94309 : Nat.Prime 94309 := by
  apply nodeValid_prime [2, 3, 29, 271] ⟨94309, 6, [(2, 2), (3, 1), (29, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_271
  · decide +kernel

theorem prime_123499 : Nat.Prime 123499 := by
  apply nodeValid_prime [2, 3, 2287] ⟨123499, 2, [(2, 1), (3, 3), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2287
  · decide +kernel

theorem prime_132757 : Nat.Prime 132757 := by
  apply nodeValid_prime [2, 3, 13, 23, 37] ⟨132757, 6, [(2, 2), (3, 1), (13, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_136093 : Nat.Prime 136093 := by
  apply nodeValid_prime [2, 3, 11, 1031] ⟨136093, 5, [(2, 2), (3, 1), (11, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1031
  · decide +kernel

theorem prime_137713 : Nat.Prime 137713 := by
  apply nodeValid_prime [2, 3, 19, 151] ⟨137713, 10, [(2, 4), (3, 1), (19, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_151
  · decide +kernel

theorem prime_139991 : Nat.Prime 139991 := by
  apply nodeValid_prime [2, 5, 13999] ⟨139991, 11, [(2, 1), (5, 1), (13999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13999
  · decide +kernel

theorem prime_145643 : Nat.Prime 145643 := by
  apply nodeValid_prime [2, 7, 101, 103] ⟨145643, 6, [(2, 1), (7, 1), (101, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_103
  · decide +kernel

theorem prime_154409 : Nat.Prime 154409 := by
  apply nodeValid_prime [2, 19301] ⟨154409, 3, [(2, 3), (19301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19301
  · decide +kernel

theorem prime_159721 : Nat.Prime 159721 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨159721, 17, [(2, 3), (3, 1), (5, 1), (11, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_191507 : Nat.Prime 191507 := by
  apply nodeValid_prime [2, 7, 13679] ⟨191507, 2, [(2, 1), (7, 1), (13679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13679
  · decide +kernel

theorem prime_209317 : Nat.Prime 209317 := by
  apply nodeValid_prime [2, 3, 17443] ⟨209317, 5, [(2, 2), (3, 1), (17443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17443
  · decide +kernel

theorem prime_280037 : Nat.Prime 280037 := by
  apply nodeValid_prime [2, 70009] ⟨280037, 2, [(2, 2), (70009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_70009
  · decide +kernel

theorem prime_315893 : Nat.Prime 315893 := by
  apply nodeValid_prime [2, 151, 523] ⟨315893, 2, [(2, 2), (151, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_523
  · decide +kernel

theorem prime_375673 : Nat.Prime 375673 := by
  apply nodeValid_prime [2, 3, 11, 1423] ⟨375673, 5, [(2, 3), (3, 1), (11, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1423
  · decide +kernel

theorem prime_481549 : Nat.Prime 481549 := by
  apply nodeValid_prime [2, 3, 40129] ⟨481549, 2, [(2, 2), (3, 1), (40129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40129
  · decide +kernel

theorem prime_626533 : Nat.Prime 626533 := by
  apply nodeValid_prime [2, 3, 109, 479] ⟨626533, 2, [(2, 2), (3, 1), (109, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_479
  · decide +kernel

theorem prime_642359 : Nat.Prime 642359 := by
  apply nodeValid_prime [2, 509, 631] ⟨642359, 7, [(2, 1), (509, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_631
  · decide +kernel

theorem prime_808751 : Nat.Prime 808751 := by
  apply nodeValid_prime [2, 5, 647] ⟨808751, 11, [(2, 1), (5, 4), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_647
  · decide +kernel

theorem prime_903899 : Nat.Prime 903899 := by
  apply nodeValid_prime [2, 31, 61, 239] ⟨903899, 6, [(2, 1), (31, 1), (61, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_61
    · exact prime_239
  · decide +kernel

theorem prime_921331 : Nat.Prime 921331 := by
  apply nodeValid_prime [2, 3, 5, 29, 353] ⟨921331, 2, [(2, 1), (3, 2), (5, 1), (29, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_353
  · decide +kernel

theorem prime_1166549 : Nat.Prime 1166549 := by
  apply nodeValid_prime [2, 59, 4943] ⟨1166549, 2, [(2, 2), (59, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_4943
  · decide +kernel

theorem prime_1168357 : Nat.Prime 1168357 := by
  apply nodeValid_prime [2, 3, 7, 1987] ⟨1168357, 2, [(2, 2), (3, 1), (7, 2), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1987
  · decide +kernel

theorem prime_1211389 : Nat.Prime 1211389 := by
  apply nodeValid_prime [2, 3, 29, 59] ⟨1211389, 10, [(2, 2), (3, 1), (29, 1), (59, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_59
  · decide +kernel

theorem prime_1228291 : Nat.Prime 1228291 := by
  apply nodeValid_prime [2, 3, 5, 7, 5849] ⟨1228291, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (5849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_5849
  · decide +kernel

theorem prime_1304627 : Nat.Prime 1304627 := by
  apply nodeValid_prime [2, 47, 13879] ⟨1304627, 2, [(2, 1), (47, 1), (13879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_13879
  · decide +kernel

theorem prime_1368737 : Nat.Prime 1368737 := by
  apply nodeValid_prime [2, 42773] ⟨1368737, 3, [(2, 5), (42773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42773
  · decide +kernel

theorem prime_1476719 : Nat.Prime 1476719 := by
  apply nodeValid_prime [2, 19, 38861] ⟨1476719, 17, [(2, 1), (19, 1), (38861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_38861
  · decide +kernel

theorem prime_1637677 : Nat.Prime 1637677 := by
  apply nodeValid_prime [2, 3, 45491] ⟨1637677, 2, [(2, 2), (3, 2), (45491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45491
  · decide +kernel

theorem prime_1864117 : Nat.Prime 1864117 := by
  apply nodeValid_prime [2, 3, 53, 977] ⟨1864117, 2, [(2, 2), (3, 2), (53, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_977
  · decide +kernel

theorem prime_2332403 : Nat.Prime 2332403 := by
  apply nodeValid_prime [2, 19, 61379] ⟨2332403, 2, [(2, 1), (19, 1), (61379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61379
  · decide +kernel

theorem prime_2953439 : Nat.Prime 2953439 := by
  apply nodeValid_prime [2, 1476719] ⟨2953439, 11, [(2, 1), (1476719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1476719
  · decide +kernel

theorem prime_4369291 : Nat.Prime 4369291 := by
  apply nodeValid_prime [2, 3, 5, 145643] ⟨4369291, 2, [(2, 1), (3, 1), (5, 1), (145643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_145643
  · decide +kernel

theorem prime_4422503 : Nat.Prime 4422503 := by
  apply nodeValid_prime [2, 7, 315893] ⟨4422503, 7, [(2, 1), (7, 1), (315893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_315893
  · decide +kernel

theorem prime_4664173 : Nat.Prime 4664173 := by
  apply nodeValid_prime [2, 3, 197, 1973] ⟨4664173, 5, [(2, 2), (3, 1), (197, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1973
  · decide +kernel

theorem prime_6313459 : Nat.Prime 6313459 := by
  apply nodeValid_prime [2, 3, 37, 28439] ⟨6313459, 2, [(2, 1), (3, 1), (37, 1), (28439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_28439
  · decide +kernel

theorem prime_6372337 : Nat.Prime 6372337 := by
  apply nodeValid_prime [2, 3, 132757] ⟨6372337, 7, [(2, 4), (3, 1), (132757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132757
  · decide +kernel

theorem prime_7294543 : Nat.Prime 7294543 := by
  apply nodeValid_prime [2, 3, 23, 52859] ⟨7294543, 3, [(2, 1), (3, 1), (23, 1), (52859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_52859
  · decide +kernel

theorem prime_8227781 : Nat.Prime 8227781 := by
  apply nodeValid_prime [2, 5, 11, 149, 251] ⟨8227781, 2, [(2, 2), (5, 1), (11, 1), (149, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_149
    · exact prime_251
  · decide +kernel

theorem prime_9570131 : Nat.Prime 9570131 := by
  apply nodeValid_prime [2, 5, 641, 1493] ⟨9570131, 2, [(2, 1), (5, 1), (641, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
    · exact prime_1493
  · decide +kernel

theorem prime_9950081 : Nat.Prime 9950081 := by
  apply nodeValid_prime [2, 5, 7, 2221] ⟨9950081, 3, [(2, 7), (5, 1), (7, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2221
  · decide +kernel

theorem prime_10064819 : Nat.Prime 10064819 := by
  apply nodeValid_prime [2, 71, 70879] ⟨10064819, 2, [(2, 1), (71, 1), (70879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_70879
  · decide +kernel

theorem prime_15778267 : Nat.Prime 15778267 := by
  apply nodeValid_prime [2, 3, 7, 375673] ⟨15778267, 3, [(2, 1), (3, 1), (7, 1), (375673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_375673
  · decide +kernel

theorem prime_17280811 : Nat.Prime 17280811 := by
  apply nodeValid_prime [2, 3, 5, 29, 2207] ⟨17280811, 3, [(2, 1), (3, 3), (5, 1), (29, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_2207
  · decide +kernel

theorem prime_18514009 : Nat.Prime 18514009 := by
  apply nodeValid_prime [2, 3, 28571] ⟨18514009, 7, [(2, 3), (3, 4), (28571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28571
  · decide +kernel

theorem prime_33087673 : Nat.Prime 33087673 := by
  apply nodeValid_prime [2, 3, 59, 7789] ⟨33087673, 5, [(2, 3), (3, 2), (59, 1), (7789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_7789
  · decide +kernel

theorem prime_36911353 : Nat.Prime 36911353 := by
  apply nodeValid_prime [2, 3, 17, 90469] ⟨36911353, 7, [(2, 3), (3, 1), (17, 1), (90469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_90469
  · decide +kernel

theorem prime_40079947 : Nat.Prime 40079947 := by
  apply nodeValid_prime [2, 3, 1213, 5507] ⟨40079947, 3, [(2, 1), (3, 1), (1213, 1), (5507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1213
    · exact prime_5507
  · decide +kernel

theorem prime_42691031 : Nat.Prime 42691031 := by
  apply nodeValid_prime [2, 5, 31, 137713] ⟨42691031, 11, [(2, 1), (5, 1), (31, 1), (137713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_137713
  · decide +kernel

theorem prime_59068781 : Nat.Prime 59068781 := by
  apply nodeValid_prime [2, 5, 2953439] ⟨59068781, 2, [(2, 2), (5, 1), (2953439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2953439
  · decide +kernel

theorem prime_73637227 : Nat.Prime 73637227 := by
  apply nodeValid_prime [2, 3, 13, 137, 2297] ⟨73637227, 2, [(2, 1), (3, 2), (13, 1), (137, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_137
    · exact prime_2297
  · decide +kernel

theorem prime_77290159 : Nat.Prime 77290159 := by
  apply nodeValid_prime [2, 3, 11, 157, 7459] ⟨77290159, 6, [(2, 1), (3, 1), (11, 1), (157, 1), (7459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_157
    · exact prime_7459
  · decide +kernel

theorem prime_115038611 : Nat.Prime 115038611 := by
  apply nodeValid_prime [2, 5, 47, 157, 1559] ⟨115038611, 2, [(2, 1), (5, 1), (47, 1), (157, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_157
    · exact prime_1559
  · decide +kernel

theorem prime_116157071 : Nat.Prime 116157071 := by
  apply nodeValid_prime [2, 5, 19, 101, 6053] ⟨116157071, 7, [(2, 1), (5, 1), (19, 1), (101, 1), (6053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_101
    · exact prime_6053
  · decide +kernel

theorem prime_121919723 : Nat.Prime 121919723 := by
  apply nodeValid_prime [2, 1063, 57347] ⟨121919723, 2, [(2, 1), (1063, 1), (57347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1063
    · exact prime_57347
  · decide +kernel

theorem prime_123922471 : Nat.Prime 123922471 := by
  apply nodeValid_prime [2, 3, 5, 7, 12043] ⟨123922471, 3, [(2, 1), (3, 1), (5, 1), (7, 3), (12043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_12043
  · decide +kernel

theorem prime_142273099 : Nat.Prime 142273099 := by
  apply nodeValid_prime [2, 3, 11, 2957] ⟨142273099, 3, [(2, 1), (3, 7), (11, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2957
  · decide +kernel

theorem prime_156631621 : Nat.Prime 156631621 := by
  apply nodeValid_prime [2, 3, 5, 617, 4231] ⟨156631621, 6, [(2, 2), (3, 1), (5, 1), (617, 1), (4231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_617
    · exact prime_4231
  · decide +kernel

theorem prime_174682163 : Nat.Prime 174682163 := by
  apply nodeValid_prime [2, 19, 61, 179, 421] ⟨174682163, 5, [(2, 1), (19, 1), (61, 1), (179, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
    · exact prime_179
    · exact prime_421
  · decide +kernel

theorem prime_222121751 : Nat.Prime 222121751 := by
  apply nodeValid_prime [2, 5, 67, 89, 149] ⟨222121751, 13, [(2, 1), (5, 3), (67, 1), (89, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_89
    · exact prime_149
  · decide +kernel

theorem prime_232314143 : Nat.Prime 232314143 := by
  apply nodeValid_prime [2, 116157071] ⟨232314143, 5, [(2, 1), (116157071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_116157071
  · decide +kernel

theorem prime_249609671 : Nat.Prime 249609671 := by
  apply nodeValid_prime [2, 5, 29, 491, 1753] ⟨249609671, 11, [(2, 1), (5, 1), (29, 1), (491, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_491
    · exact prime_1753
  · decide +kernel

theorem prime_267382811 : Nat.Prime 267382811 := by
  apply nodeValid_prime [2, 5, 191, 139991] ⟨267382811, 2, [(2, 1), (5, 1), (191, 1), (139991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
    · exact prime_139991
  · decide +kernel

theorem prime_269547253 : Nat.Prime 269547253 := by
  apply nodeValid_prime [2, 3, 13, 359, 4813] ⟨269547253, 2, [(2, 2), (3, 1), (13, 1), (359, 1), (4813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_359
    · exact prime_4813
  · decide +kernel

theorem prime_287538109 : Nat.Prime 287538109 := by
  apply nodeValid_prime [2, 3, 11, 13, 15233] ⟨287538109, 2, [(2, 2), (3, 1), (11, 2), (13, 1), (15233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_15233
  · decide +kernel

theorem prime_569092397 : Nat.Prime 569092397 := by
  apply nodeValid_prime [2, 142273099] ⟨569092397, 2, [(2, 2), (142273099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_142273099
  · decide +kernel

theorem prime_586312277 : Nat.Prime 586312277 := by
  apply nodeValid_prime [2, 11, 1211389] ⟨586312277, 5, [(2, 2), (11, 2), (1211389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1211389
  · decide +kernel

theorem prime_780992923 : Nat.Prime 780992923 := by
  apply nodeValid_prime [2, 3, 23, 1699, 3331] ⟨780992923, 2, [(2, 1), (3, 1), (23, 1), (1699, 1), (3331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1699
    · exact prime_3331
  · decide +kernel

theorem prime_820001719 : Nat.Prime 820001719 := by
  apply nodeValid_prime [2, 3, 137, 36947] ⟨820001719, 6, [(2, 1), (3, 4), (137, 1), (36947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_36947
  · decide +kernel

theorem prime_1327701083 : Nat.Prime 1327701083 := by
  apply nodeValid_prime [2, 23, 449, 64283] ⟨1327701083, 2, [(2, 1), (23, 1), (449, 1), (64283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_449
    · exact prime_64283
  · decide +kernel

theorem prime_1496684383 : Nat.Prime 1496684383 := by
  apply nodeValid_prime [2, 3, 23, 757, 14327] ⟨1496684383, 3, [(2, 1), (3, 1), (23, 1), (757, 1), (14327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_757
    · exact prime_14327
  · decide +kernel

theorem prime_1752535501 : Nat.Prime 1752535501 := by
  apply nodeValid_prime [2, 3, 5, 1168357] ⟨1752535501, 2, [(2, 2), (3, 1), (5, 3), (1168357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1168357
  · decide +kernel

theorem prime_2224065251 : Nat.Prime 2224065251 := by
  apply nodeValid_prime [2, 5, 11, 808751] ⟨2224065251, 2, [(2, 1), (5, 3), (11, 1), (808751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_808751
  · decide +kernel

theorem prime_2240235089 : Nat.Prime 2240235089 := by
  apply nodeValid_prime [2, 7, 13, 31, 49633] ⟨2240235089, 3, [(2, 4), (7, 1), (13, 1), (31, 1), (49633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_49633
  · decide +kernel

theorem prime_3642193649 : Nat.Prime 3642193649 := by
  apply nodeValid_prime [2, 139, 1637677] ⟨3642193649, 3, [(2, 4), (139, 1), (1637677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_1637677
  · decide +kernel

theorem prime_6050935837 : Nat.Prime 6050935837 := by
  apply nodeValid_prime [2, 3, 11, 73, 209317] ⟨6050935837, 5, [(2, 2), (3, 2), (11, 1), (73, 1), (209317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_209317
  · decide +kernel

theorem prime_8261645551 : Nat.Prime 8261645551 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 41, 4159] ⟨8261645551, 6, [(2, 1), (3, 1), (5, 2), (17, 1), (19, 1), (41, 1), (4159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_41
    · exact prime_4159
  · decide +kernel

theorem prime_10890031681 : Nat.Prime 10890031681 := by
  apply nodeValid_prime [2, 3, 5, 11, 173, 1987] ⟨10890031681, 23, [(2, 6), (3, 2), (5, 1), (11, 1), (173, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_173
    · exact prime_1987
  · decide +kernel

theorem prime_15283324417 : Nat.Prime 15283324417 := by
  apply nodeValid_prime [2, 3, 9950081] ⟨15283324417, 5, [(2, 9), (3, 1), (9950081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9950081
  · decide +kernel

theorem prime_18591427831 : Nat.Prime 18591427831 := by
  apply nodeValid_prime [2, 3, 5, 113, 1033, 5309] ⟨18591427831, 3, [(2, 1), (3, 1), (5, 1), (113, 1), (1033, 1), (5309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_1033
    · exact prime_5309
  · decide +kernel

theorem prime_35224384781 : Nat.Prime 35224384781 := by
  apply nodeValid_prime [2, 5, 13, 1097, 123499] ⟨35224384781, 3, [(2, 2), (5, 1), (13, 1), (1097, 1), (123499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1097
    · exact prime_123499
  · decide +kernel

theorem prime_37312224143 : Nat.Prime 37312224143 := by
  apply nodeValid_prime [2, 337, 587, 94309] ⟨37312224143, 5, [(2, 1), (337, 1), (587, 1), (94309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_587
    · exact prime_94309
  · decide +kernel

theorem prime_43618565719 : Nat.Prime 43618565719 := by
  apply nodeValid_prime [2, 3, 7, 13, 53, 991] ⟨43618565719, 7, [(2, 1), (3, 3), (7, 1), (13, 3), (53, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_53
    · exact prime_991
  · decide +kernel

theorem prime_69148738819 : Nat.Prime 69148738819 := by
  apply nodeValid_prime [2, 3, 31, 123922471] ⟨69148738819, 2, [(2, 1), (3, 2), (31, 1), (123922471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_123922471
  · decide +kernel

theorem prime_92030888801 : Nat.Prime 92030888801 := by
  apply nodeValid_prime [2, 5, 115038611] ⟨92030888801, 3, [(2, 5), (5, 2), (115038611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_115038611
  · decide +kernel

theorem prime_195757833811 : Nat.Prime 195757833811 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 353, 431, 557] ⟨195757833811, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (353, 1), (431, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_353
    · exact prime_431
    · exact prime_557
  · decide +kernel

theorem prime_436185657191 : Nat.Prime 436185657191 := by
  apply nodeValid_prime [2, 5, 43618565719] ⟨436185657191, 7, [(2, 1), (5, 1), (43618565719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43618565719
  · decide +kernel

theorem prime_438235201531 : Nat.Prime 438235201531 := by
  apply nodeValid_prime [2, 3, 5, 7, 77290159] ⟨438235201531, 10, [(2, 1), (3, 4), (5, 1), (7, 1), (77290159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_77290159
  · decide +kernel

theorem prime_654717078581 : Nat.Prime 654717078581 := by
  apply nodeValid_prime [2, 5, 997, 1523, 21559] ⟨654717078581, 2, [(2, 2), (5, 1), (997, 1), (1523, 1), (21559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_997
    · exact prime_1523
    · exact prime_21559
  · decide +kernel

theorem prime_978132762689 : Nat.Prime 978132762689 := by
  apply nodeValid_prime [2, 15283324417] ⟨978132762689, 3, [(2, 6), (15283324417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15283324417
  · decide +kernel

theorem prime_1302427837631 : Nat.Prime 1302427837631 := by
  apply nodeValid_prime [2, 5, 202757, 642359] ⟨1302427837631, 7, [(2, 1), (5, 1), (202757, 1), (642359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_202757
    · exact prime_642359
  · decide +kernel

theorem prime_1317346703731 : Nat.Prime 1317346703731 := by
  apply nodeValid_prime [2, 3, 5, 15887, 921331] ⟨1317346703731, 2, [(2, 1), (3, 2), (5, 1), (15887, 1), (921331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15887
    · exact prime_921331
  · decide +kernel

theorem prime_1969420304539 : Nat.Prime 1969420304539 := by
  apply nodeValid_prime [2, 3, 277, 2473, 159721] ⟨1969420304539, 3, [(2, 1), (3, 2), (277, 1), (2473, 1), (159721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_2473
    · exact prime_159721
  · decide +kernel

theorem prime_3923040602993 : Nat.Prime 3923040602993 := by
  apply nodeValid_prime [2, 7, 131, 267382811] ⟨3923040602993, 3, [(2, 4), (7, 1), (131, 1), (267382811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_267382811
  · decide +kernel

theorem prime_7793605354159 : Nat.Prime 7793605354159 := by
  apply nodeValid_prime [2, 3, 13, 17, 19, 47, 613, 1193] ⟨7793605354159, 3, [(2, 1), (3, 3), (13, 1), (17, 1), (19, 1), (47, 1), (613, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_47
    · exact prime_613
    · exact prime_1193
  · decide +kernel

theorem prime_7793605357211 : Nat.Prime 7793605357211 := by
  apply nodeValid_prime [2, 5, 587, 1327701083] ⟨7793605357211, 2, [(2, 1), (5, 1), (587, 1), (1327701083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_587
    · exact prime_1327701083
  · decide +kernel

theorem prime_7793605358057 : Nat.Prime 7793605358057 := by
  apply nodeValid_prime [2, 7, 23, 6050935837] ⟨7793605358057, 3, [(2, 3), (7, 1), (23, 1), (6050935837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_6050935837
  · decide +kernel

theorem prime_7798842195329 : Nat.Prime 7798842195329 := by
  apply nodeValid_prime [2, 31, 3137, 626533] ⟨7798842195329, 3, [(2, 7), (31, 1), (3137, 1), (626533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3137
    · exact prime_626533
  · decide +kernel

theorem prime_7798842208489 : Nat.Prime 7798842208489 := by
  apply nodeValid_prime [2, 3, 571, 569092397] ⟨7798842208489, 14, [(2, 3), (3, 1), (571, 1), (569092397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_571
    · exact prime_569092397
  · decide +kernel

theorem prime_7798842208753 : Nat.Prime 7798842208753 := by
  apply nodeValid_prime [2, 3, 7, 19, 6379, 191507] ⟨7798842208753, 10, [(2, 4), (3, 1), (7, 1), (19, 1), (6379, 1), (191507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_6379
    · exact prime_191507
  · decide +kernel

theorem prime_7804081417637 : Nat.Prime 7804081417637 := by
  apply nodeValid_prime [2, 7, 19, 2011, 7294543] ⟨7804081417637, 2, [(2, 2), (7, 1), (19, 1), (2011, 1), (7294543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_2011
    · exact prime_7294543
  · decide +kernel

theorem prime_7804081468891 : Nat.Prime 7804081468891 := by
  apply nodeValid_prime [2, 3, 5, 7, 2801, 4422503] ⟨7804081468891, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (2801, 1), (4422503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2801
    · exact prime_4422503
  · decide +kernel

theorem prime_7804081469231 : Nat.Prime 7804081469231 := by
  apply nodeValid_prime [2, 5, 37, 173, 121919723] ⟨7804081469231, 13, [(2, 1), (5, 1), (37, 1), (173, 1), (121919723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_173
    · exact prime_121919723
  · decide +kernel

theorem prime_7809323013917 : Nat.Prime 7809323013917 := by
  apply nodeValid_prime [2, 7243, 269547253] ⟨7809323013917, 2, [(2, 2), (7243, 1), (269547253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7243
    · exact prime_269547253
  · decide +kernel

theorem prime_7809323017079 : Nat.Prime 7809323017079 := by
  apply nodeValid_prime [2, 11, 47, 757, 1949, 5119] ⟨7809323017079, 11, [(2, 1), (11, 1), (47, 1), (757, 1), (1949, 1), (5119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_757
    · exact prime_1949
    · exact prime_5119
  · decide +kernel

theorem prime_7809323028431 : Nat.Prime 7809323028431 := by
  apply nodeValid_prime [2, 5, 7, 11, 227, 2243, 19919] ⟨7809323028431, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (227, 1), (2243, 1), (19919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_227
    · exact prime_2243
    · exact prime_19919
  · decide +kernel

theorem prime_7814567025787 : Nat.Prime 7814567025787 := by
  apply nodeValid_prime [2, 3, 1302427837631] ⟨7814567025787, 2, [(2, 1), (3, 1), (1302427837631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1302427837631
  · decide +kernel

theorem prime_7814567027257 : Nat.Prime 7814567027257 := by
  apply nodeValid_prime [2, 3, 11, 17, 173, 10064819] ⟨7814567027257, 5, [(2, 3), (3, 1), (11, 1), (17, 1), (173, 1), (10064819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_173
    · exact prime_10064819
  · decide +kernel

theorem prime_7814567029099 : Nat.Prime 7814567029099 := by
  apply nodeValid_prime [2, 3, 136093, 9570131] ⟨7814567029099, 3, [(2, 1), (3, 1), (136093, 1), (9570131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_136093
    · exact prime_9570131
  · decide +kernel

theorem prime_7819813405463 : Nat.Prime 7819813405463 := by
  apply nodeValid_prime [2, 23, 97, 1752535501] ⟨7819813405463, 5, [(2, 1), (23, 1), (97, 1), (1752535501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_97
    · exact prime_1752535501
  · decide +kernel

theorem prime_7819813421383 : Nat.Prime 7819813421383 := by
  apply nodeValid_prime [2, 3, 37, 35224384781] ⟨7819813421383, 5, [(2, 1), (3, 1), (37, 1), (35224384781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_35224384781
  · decide +kernel

theorem prime_7819813422517 : Nat.Prime 7819813422517 := by
  apply nodeValid_prime [2, 3, 293, 2224065251] ⟨7819813422517, 2, [(2, 2), (3, 1), (293, 1), (2224065251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_2224065251
  · decide +kernel

theorem prime_7825062098327 : Nat.Prime 7825062098327 := by
  apply nodeValid_prime [2, 11, 1237, 287538109] ⟨7825062098327, 5, [(2, 1), (11, 1), (1237, 1), (287538109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1237
    · exact prime_287538109
  · decide +kernel

theorem prime_7825062101513 : Nat.Prime 7825062101513 := by
  apply nodeValid_prime [2, 978132762689] ⟨7825062101513, 3, [(2, 3), (978132762689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_978132762689
  · decide +kernel

theorem prime_7825062173749 : Nat.Prime 7825062173749 := by
  apply nodeValid_prime [2, 3, 3733, 174682163] ⟨7825062173749, 6, [(2, 2), (3, 1), (3733, 1), (174682163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3733
    · exact prime_174682163
  · decide +kernel

theorem prime_7830313337741 : Nat.Prime 7830313337741 := by
  apply nodeValid_prime [2, 5, 41, 43, 11003, 20183] ⟨7830313337741, 2, [(2, 2), (5, 1), (41, 1), (43, 1), (11003, 1), (20183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_43
    · exact prime_11003
    · exact prime_20183
  · decide +kernel

theorem prime_7830313352441 : Nat.Prime 7830313352441 := by
  apply nodeValid_prime [2, 5, 195757833811] ⟨7830313352441, 3, [(2, 3), (5, 1), (195757833811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_195757833811
  · decide +kernel

theorem prime_7830313355453 : Nat.Prime 7830313355453 := by
  apply nodeValid_prime [2, 7, 41, 829, 8227781] ⟨7830313355453, 2, [(2, 2), (7, 1), (41, 1), (829, 1), (8227781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_829
    · exact prime_8227781
  · decide +kernel

theorem prime_7835566888277 : Nat.Prime 7835566888277 := by
  apply nodeValid_prime [2, 8819, 222121751] ⟨7835566888277, 2, [(2, 2), (8819, 1), (222121751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8819
    · exact prime_222121751
  · decide +kernel

theorem prime_7835567070031 : Nat.Prime 7835567070031 := by
  apply nodeValid_prime [2, 3, 5, 7, 37312224143] ⟨7835567070031, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (37312224143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37312224143
  · decide +kernel

theorem prime_7840822810321 : Nat.Prime 7840822810321 := by
  apply nodeValid_prime [2, 3, 5, 10890031681] ⟨7840822810321, 11, [(2, 4), (3, 2), (5, 1), (10890031681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10890031681
  · decide +kernel

theorem prime_7840822811501 : Nat.Prime 7840822811501 := by
  apply nodeValid_prime [2, 5, 7, 2240235089] ⟨7840822811501, 10, [(2, 2), (5, 3), (7, 1), (2240235089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2240235089
  · decide +kernel

theorem prime_7840822827763 : Nat.Prime 7840822827763 := by
  apply nodeValid_prime [2, 3, 53, 4409, 1864117] ⟨7840822827763, 5, [(2, 1), (3, 2), (53, 1), (4409, 1), (1864117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_4409
    · exact prime_1864117
  · decide +kernel

theorem prime_7846081148947 : Nat.Prime 7846081148947 := by
  apply nodeValid_prime [2, 3, 251, 1117, 4664173] ⟨7846081148947, 2, [(2, 1), (3, 1), (251, 1), (1117, 1), (4664173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_1117
    · exact prime_4664173
  · decide +kernel

theorem prime_7846081205539 : Nat.Prime 7846081205539 := by
  apply nodeValid_prime [2, 3, 61, 107, 677, 295937] ⟨7846081205539, 3, [(2, 1), (3, 1), (61, 1), (107, 1), (677, 1), (295937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_107
    · exact prime_677
    · exact prime_295937
  · decide +kernel

theorem prime_7846081205987 : Nat.Prime 7846081205987 := by
  apply nodeValid_prime [2, 3923040602993] ⟨7846081205987, 2, [(2, 1), (3923040602993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3923040602993
  · decide +kernel

theorem prime_7851341828399 : Nat.Prime 7851341828399 := by
  apply nodeValid_prime [2, 67, 97, 463, 1304627] ⟨7851341828399, 11, [(2, 1), (67, 1), (97, 1), (463, 1), (1304627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_97
    · exact prime_463
    · exact prime_1304627
  · decide +kernel

theorem prime_7851341829439 : Nat.Prime 7851341829439 := by
  apply nodeValid_prime [2, 3, 436185657191] ⟨7851341829439, 6, [(2, 1), (3, 2), (436185657191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_436185657191
  · decide +kernel

theorem prime_7851341850893 : Nat.Prime 7851341850893 := by
  apply nodeValid_prime [2, 19, 16363, 6313459] ⟨7851341850893, 2, [(2, 2), (19, 1), (16363, 1), (6313459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_16363
    · exact prime_6313459
  · decide +kernel

theorem prime_7856604858689 : Nat.Prime 7856604858689 := by
  apply nodeValid_prime [2, 47, 2239, 1166549] ⟨7856604858689, 3, [(2, 6), (47, 1), (2239, 1), (1166549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_2239
    · exact prime_1166549
  · decide +kernel

theorem prime_7856604859241 : Nat.Prime 7856604859241 := by
  apply nodeValid_prime [2, 5, 103, 18514009] ⟨7856604859241, 6, [(2, 3), (5, 1), (103, 2), (18514009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_18514009
  · decide +kernel

theorem prime_7856604942973 : Nat.Prime 7856604942973 := by
  apply nodeValid_prime [2, 3, 654717078581] ⟨7856604942973, 5, [(2, 2), (3, 1), (654717078581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_654717078581
  · decide +kernel

theorem prime_7861870402829 : Nat.Prime 7861870402829 := by
  apply nodeValid_prime [2, 13, 673, 17280811] ⟨7861870402829, 2, [(2, 2), (13, 2), (673, 1), (17280811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_673
    · exact prime_17280811
  · decide +kernel

theorem prime_7861870402921 : Nat.Prime 7861870402921 := by
  apply nodeValid_prime [2, 3, 5, 47, 20641, 22511] ⟨7861870402921, 11, [(2, 3), (3, 2), (5, 1), (47, 1), (20641, 1), (22511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_20641
    · exact prime_22511
  · decide +kernel

theorem prime_7861870419539 : Nat.Prime 7861870419539 := by
  apply nodeValid_prime [2, 613, 72077, 88969] ⟨7861870419539, 2, [(2, 1), (613, 1), (72077, 1), (88969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_72077
    · exact prime_88969
  · decide +kernel

theorem prime_7867138132787 : Nat.Prime 7867138132787 := by
  apply nodeValid_prime [2, 6709, 586312277] ⟨7867138132787, 2, [(2, 1), (6709, 1), (586312277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6709
    · exact prime_586312277
  · decide +kernel

theorem prime_7867138133009 : Nat.Prime 7867138133009 := by
  apply nodeValid_prime [2, 7, 11, 173, 36911353] ⟨7867138133009, 3, [(2, 4), (7, 1), (11, 1), (173, 1), (36911353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_173
    · exact prime_36911353
  · decide +kernel

theorem prime_7867138281841 : Nat.Prime 7867138281841 := by
  apply nodeValid_prime [2, 3, 5, 3642193649] ⟨7867138281841, 7, [(2, 4), (3, 3), (5, 1), (3642193649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3642193649
  · decide +kernel

theorem prime_7872408536981 : Nat.Prime 7872408536981 := by
  apply nodeValid_prime [2, 5, 13, 19, 101, 15778267] ⟨7872408536981, 2, [(2, 2), (5, 1), (13, 1), (19, 1), (101, 1), (15778267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_101
    · exact prime_15778267
  · decide +kernel

theorem prime_7872408663841 : Nat.Prime 7872408663841 := by
  apply nodeValid_prime [2, 3, 5, 7, 780992923] ⟨7872408663841, 13, [(2, 5), (3, 2), (5, 1), (7, 1), (780992923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_780992923
  · decide +kernel

theorem prime_7872408664117 : Nat.Prime 7872408664117 := by
  apply nodeValid_prime [2, 3, 59, 151, 73637227] ⟨7872408664117, 6, [(2, 2), (3, 1), (59, 1), (151, 1), (73637227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_151
    · exact prime_73637227
  · decide +kernel

theorem prime_7877681177231 : Nat.Prime 7877681177231 := by
  apply nodeValid_prime [2, 5, 53, 12101, 1228291] ⟨7877681177231, 13, [(2, 1), (5, 1), (53, 1), (12101, 1), (1228291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_12101
    · exact prime_1228291
  · decide +kernel

theorem prime_7877681216761 : Nat.Prime 7877681216761 := by
  apply nodeValid_prime [2, 3, 5, 263, 249609671] ⟨7877681216761, 13, [(2, 3), (3, 1), (5, 1), (263, 1), (249609671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
    · exact prime_249609671
  · decide +kernel

theorem prime_7877681218157 : Nat.Prime 7877681218157 := by
  apply nodeValid_prime [2, 1969420304539] ⟨7877681218157, 2, [(2, 2), (1969420304539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1969420304539
  · decide +kernel

theorem prime_7882956207961 : Nat.Prime 7882956207961 := by
  apply nodeValid_prime [2, 3, 5, 467, 911, 154409] ⟨7882956207961, 11, [(2, 3), (3, 1), (5, 1), (467, 1), (911, 1), (154409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
    · exact prime_911
    · exact prime_154409
  · decide +kernel

theorem prime_7882956221689 : Nat.Prime 7882956221689 := by
  apply nodeValid_prime [2, 3, 233, 156631621] ⟨7882956221689, 7, [(2, 3), (3, 3), (233, 1), (156631621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_156631621
  · decide +kernel

theorem prime_7882956225367 : Nat.Prime 7882956225367 := by
  apply nodeValid_prime [2, 3, 19, 69148738819] ⟨7882956225367, 5, [(2, 1), (3, 1), (19, 1), (69148738819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_69148738819
  · decide +kernel

theorem prime_7888233593893 : Nat.Prime 7888233593893 := by
  apply nodeValid_prime [2, 3, 19867, 33087673] ⟨7888233593893, 5, [(2, 2), (3, 1), (19867, 1), (33087673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19867
    · exact prime_33087673
  · decide +kernel

theorem prime_7888233594061 : Nat.Prime 7888233594061 := by
  apply nodeValid_prime [2, 3, 5, 6263, 2332403] ⟨7888233594061, 14, [(2, 2), (3, 3), (5, 1), (6263, 1), (2332403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6263
    · exact prime_2332403
  · decide +kernel

theorem prime_7888233627559 : Nat.Prime 7888233627559 := by
  apply nodeValid_prime [2, 3, 438235201531] ⟨7888233627559, 3, [(2, 1), (3, 2), (438235201531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_438235201531
  · decide +kernel

theorem prime_7893513435943 : Nat.Prime 7893513435943 := by
  apply nodeValid_prime [2, 3, 293, 1496684383] ⟨7893513435943, 5, [(2, 1), (3, 2), (293, 1), (1496684383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_1496684383
  · decide +kernel

theorem prime_7893513438719 : Nat.Prime 7893513438719 := by
  apply nodeValid_prime [2, 19, 23, 137, 4231, 15581] ⟨7893513438719, 17, [(2, 1), (19, 1), (23, 1), (137, 1), (4231, 1), (15581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_137
    · exact prime_4231
    · exact prime_15581
  · decide +kernel

theorem prime_7898795531219 : Nat.Prime 7898795531219 := by
  apply nodeValid_prime [2, 903899, 4369291] ⟨7898795531219, 2, [(2, 1), (903899, 1), (4369291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_903899
    · exact prime_4369291
  · decide +kernel

theorem prime_7898795532883 : Nat.Prime 7898795532883 := by
  apply nodeValid_prime [2, 3, 17, 19, 23, 59068781] ⟨7898795532883, 2, [(2, 1), (3, 2), (17, 1), (19, 1), (23, 1), (59068781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_23
    · exact prime_59068781
  · decide +kernel

theorem prime_7898795634973 : Nat.Prime 7898795634973 := by
  apply nodeValid_prime [2, 3, 11, 1493, 40079947] ⟨7898795634973, 2, [(2, 2), (3, 1), (11, 1), (1493, 1), (40079947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1493
    · exact prime_40079947
  · decide +kernel

theorem prime_7904080169173 : Nat.Prime 7904080169173 := by
  apply nodeValid_prime [2, 3, 11, 37, 9209, 58579] ⟨7904080169173, 2, [(2, 2), (3, 2), (11, 1), (37, 1), (9209, 1), (58579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_9209
    · exact prime_58579
  · decide +kernel

theorem prime_7904080169737 : Nat.Prime 7904080169737 := by
  apply nodeValid_prime [2, 3, 31, 59, 643, 280037] ⟨7904080169737, 7, [(2, 3), (3, 1), (31, 1), (59, 1), (643, 1), (280037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_59
    · exact prime_643
    · exact prime_280037
  · decide +kernel

theorem prime_7904080222387 : Nat.Prime 7904080222387 := by
  apply nodeValid_prime [2, 3, 1317346703731] ⟨7904080222387, 3, [(2, 1), (3, 1), (1317346703731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1317346703731
  · decide +kernel

theorem prime_7909367203357 : Nat.Prime 7909367203357 := by
  apply nodeValid_prime [2, 3, 481549, 1368737] ⟨7909367203357, 5, [(2, 2), (3, 1), (481549, 1), (1368737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_481549
    · exact prime_1368737
  · decide +kernel

theorem prime_7909367312579 : Nat.Prime 7909367312579 := by
  apply nodeValid_prime [2, 29, 587, 232314143] ⟨7909367312579, 2, [(2, 1), (29, 1), (587, 1), (232314143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_587
    · exact prime_232314143
  · decide +kernel

theorem prime_7909367313371 : Nat.Prime 7909367313371 := by
  apply nodeValid_prime [2, 5, 97, 191, 42691031] ⟨7909367313371, 2, [(2, 1), (5, 1), (97, 1), (191, 1), (42691031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_191
    · exact prime_42691031
  · decide +kernel

theorem prime_7914656436887 : Nat.Prime 7914656436887 := by
  apply nodeValid_prime [2, 43, 92030888801] ⟨7914656436887, 5, [(2, 1), (43, 1), (92030888801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_92030888801
  · decide +kernel

theorem prime_7914656437859 : Nat.Prime 7914656437859 := by
  apply nodeValid_prime [2, 479, 8261645551] ⟨7914656437859, 2, [(2, 1), (479, 1), (8261645551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_8261645551
  · decide +kernel

theorem prime_7914656591789 : Nat.Prime 7914656591789 := by
  apply nodeValid_prime [2, 19, 127, 820001719] ⟨7914656591789, 2, [(2, 2), (19, 1), (127, 1), (820001719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_127
    · exact prime_820001719
  · decide +kernel

theorem prime_7919948253169 : Nat.Prime 7919948253169 := by
  apply nodeValid_prime [2, 3, 7, 137, 6372337] ⟨7919948253169, 19, [(2, 4), (3, 4), (7, 1), (137, 1), (6372337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_6372337
  · decide +kernel

theorem prime_7919948256007 : Nat.Prime 7919948256007 := by
  apply nodeValid_prime [2, 3, 71, 18591427831] ⟨7919948256007, 3, [(2, 1), (3, 1), (71, 1), (18591427831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_18591427831
  · decide +kernel

theorem prime_7919948381161 : Nat.Prime 7919948381161 := by
  apply nodeValid_prime [2, 3, 5, 59, 15101, 74077] ⟨7919948381161, 7, [(2, 3), (3, 1), (5, 1), (59, 1), (15101, 1), (74077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_15101
    · exact prime_74077
  · decide +kernel

end Sude.Lucas.Generated
