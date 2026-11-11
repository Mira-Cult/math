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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1933 : Nat.Prime 1933 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨1933, 5, [(2, 2), (3, 1), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_2309 : Nat.Prime 2309 := by
  apply nodeValid_prime [2, 577] ⟨2309, 2, [(2, 2), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_577
  · decide +kernel

theorem prime_2927 : Nat.Prime 2927 := by
  apply nodeValid_prime [2, 7, 11, 19] ⟨2927, 5, [(2, 1), (7, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_2971 : Nat.Prime 2971 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨2971, 10, [(2, 1), (3, 3), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_4349 : Nat.Prime 4349 := by
  apply nodeValid_prime [2, 1087] ⟨4349, 2, [(2, 2), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1087
  · decide +kernel

theorem prime_5347 : Nat.Prime 5347 := by
  apply nodeValid_prime [2, 3, 11] ⟨5347, 3, [(2, 1), (3, 5), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_5657 : Nat.Prime 5657 := by
  apply nodeValid_prime [2, 7, 101] ⟨5657, 3, [(2, 3), (7, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
  · decide +kernel

theorem prime_8363 : Nat.Prime 8363 := by
  apply nodeValid_prime [2, 37, 113] ⟨8363, 2, [(2, 1), (37, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_113
  · decide +kernel

theorem prime_8821 : Nat.Prime 8821 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨8821, 2, [(2, 2), (3, 2), (5, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_9157 : Nat.Prime 9157 := by
  apply nodeValid_prime [2, 3, 7, 109] ⟨9157, 6, [(2, 2), (3, 1), (7, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
  · decide +kernel

theorem prime_9439 : Nat.Prime 9439 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨9439, 22, [(2, 1), (3, 1), (11, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_12329 : Nat.Prime 12329 := by
  apply nodeValid_prime [2, 23, 67] ⟨12329, 3, [(2, 3), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_12743 : Nat.Prime 12743 := by
  apply nodeValid_prime [2, 23, 277] ⟨12743, 5, [(2, 1), (23, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_277
  · decide +kernel

theorem prime_14011 : Nat.Prime 14011 := by
  apply nodeValid_prime [2, 3, 5, 467] ⟨14011, 2, [(2, 1), (3, 1), (5, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
  · decide +kernel

theorem prime_14767 : Nat.Prime 14767 := by
  apply nodeValid_prime [2, 3, 23, 107] ⟨14767, 3, [(2, 1), (3, 1), (23, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_107
  · decide +kernel

theorem prime_16747 : Nat.Prime 16747 := by
  apply nodeValid_prime [2, 3, 2791] ⟨16747, 2, [(2, 1), (3, 1), (2791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2791
  · decide +kernel

theorem prime_16927 : Nat.Prime 16927 := by
  apply nodeValid_prime [2, 3, 7, 13, 31] ⟨16927, 6, [(2, 1), (3, 1), (7, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_18911 : Nat.Prime 18911 := by
  apply nodeValid_prime [2, 5, 31, 61] ⟨18911, 14, [(2, 1), (5, 1), (31, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_61
  · decide +kernel

theorem prime_19421 : Nat.Prime 19421 := by
  apply nodeValid_prime [2, 5, 971] ⟨19421, 3, [(2, 2), (5, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_971
  · decide +kernel

theorem prime_20147 : Nat.Prime 20147 := by
  apply nodeValid_prime [2, 7, 1439] ⟨20147, 6, [(2, 1), (7, 1), (1439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1439
  · decide +kernel

theorem prime_20731 : Nat.Prime 20731 := by
  apply nodeValid_prime [2, 3, 5, 691] ⟨20731, 2, [(2, 1), (3, 1), (5, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_691
  · decide +kernel

theorem prime_21067 : Nat.Prime 21067 := by
  apply nodeValid_prime [2, 3, 3511] ⟨21067, 2, [(2, 1), (3, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3511
  · decide +kernel

theorem prime_21787 : Nat.Prime 21787 := by
  apply nodeValid_prime [2, 3, 3631] ⟨21787, 23, [(2, 1), (3, 1), (3631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3631
  · decide +kernel

theorem prime_23549 : Nat.Prime 23549 := by
  apply nodeValid_prime [2, 7, 29] ⟨23549, 2, [(2, 2), (7, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_30931 : Nat.Prime 30931 := by
  apply nodeValid_prime [2, 3, 5, 1031] ⟨30931, 2, [(2, 1), (3, 1), (5, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1031
  · decide +kernel

theorem prime_40459 : Nat.Prime 40459 := by
  apply nodeValid_prime [2, 3, 11, 613] ⟨40459, 2, [(2, 1), (3, 1), (11, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_613
  · decide +kernel

theorem prime_40961 : Nat.Prime 40961 := by
  apply nodeValid_prime [2, 5] ⟨40961, 3, [(2, 13), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_42181 : Nat.Prime 42181 := by
  apply nodeValid_prime [2, 3, 5, 19, 37] ⟨42181, 10, [(2, 2), (3, 1), (5, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_44579 : Nat.Prime 44579 := by
  apply nodeValid_prime [2, 31, 719] ⟨44579, 2, [(2, 1), (31, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_719
  · decide +kernel

theorem prime_48049 : Nat.Prime 48049 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨48049, 17, [(2, 4), (3, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_53857 : Nat.Prime 53857 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨53857, 5, [(2, 5), (3, 2), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_54667 : Nat.Prime 54667 := by
  apply nodeValid_prime [2, 3, 3037] ⟨54667, 2, [(2, 1), (3, 2), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3037
  · decide +kernel

theorem prime_56041 : Nat.Prime 56041 := by
  apply nodeValid_prime [2, 3, 5, 467] ⟨56041, 7, [(2, 3), (3, 1), (5, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
  · decide +kernel

theorem prime_60589 : Nat.Prime 60589 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨60589, 2, [(2, 2), (3, 4), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_60607 : Nat.Prime 60607 := by
  apply nodeValid_prime [2, 3, 7, 13, 37] ⟨60607, 3, [(2, 1), (3, 2), (7, 1), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_73327 : Nat.Prime 73327 := by
  apply nodeValid_prime [2, 3, 11, 101] ⟨73327, 3, [(2, 1), (3, 1), (11, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_101
  · decide +kernel

theorem prime_79621 : Nat.Prime 79621 := by
  apply nodeValid_prime [2, 3, 5, 1327] ⟨79621, 2, [(2, 2), (3, 1), (5, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1327
  · decide +kernel

theorem prime_97927 : Nat.Prime 97927 := by
  apply nodeValid_prime [2, 3, 19, 859] ⟨97927, 3, [(2, 1), (3, 1), (19, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_859
  · decide +kernel

theorem prime_115183 : Nat.Prime 115183 := by
  apply nodeValid_prime [2, 3, 79] ⟨115183, 3, [(2, 1), (3, 6), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
  · decide +kernel

theorem prime_160031 : Nat.Prime 160031 := by
  apply nodeValid_prime [2, 5, 13, 1231] ⟨160031, 11, [(2, 1), (5, 1), (13, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1231
  · decide +kernel

theorem prime_183713 : Nat.Prime 183713 := by
  apply nodeValid_prime [2, 5741] ⟨183713, 3, [(2, 5), (5741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5741
  · decide +kernel

theorem prime_203947 : Nat.Prime 203947 := by
  apply nodeValid_prime [2, 3, 19, 1789] ⟨203947, 2, [(2, 1), (3, 1), (19, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1789
  · decide +kernel

theorem prime_225751 : Nat.Prime 225751 := by
  apply nodeValid_prime [2, 3, 5, 7, 43] ⟨225751, 6, [(2, 1), (3, 1), (5, 3), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_240631 : Nat.Prime 240631 := by
  apply nodeValid_prime [2, 3, 5, 13, 617] ⟨240631, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_617
  · decide +kernel

theorem prime_242357 : Nat.Prime 242357 := by
  apply nodeValid_prime [2, 60589] ⟨242357, 2, [(2, 2), (60589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60589
  · decide +kernel

theorem prime_243239 : Nat.Prime 243239 := by
  apply nodeValid_prime [2, 19, 37, 173] ⟨243239, 19, [(2, 1), (19, 1), (37, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_173
  · decide +kernel

theorem prime_301447 : Nat.Prime 301447 := by
  apply nodeValid_prime [2, 3, 16747] ⟨301447, 3, [(2, 1), (3, 2), (16747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16747
  · decide +kernel

theorem prime_309289 : Nat.Prime 309289 := by
  apply nodeValid_prime [2, 3, 7, 263] ⟨309289, 26, [(2, 3), (3, 1), (7, 2), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_263
  · decide +kernel

theorem prime_331697 : Nat.Prime 331697 := by
  apply nodeValid_prime [2, 20731] ⟨331697, 3, [(2, 4), (20731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20731
  · decide +kernel

theorem prime_342373 : Nat.Prime 342373 := by
  apply nodeValid_prime [2, 3, 103, 277] ⟨342373, 2, [(2, 2), (3, 1), (103, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_277
  · decide +kernel

theorem prime_451553 : Nat.Prime 451553 := by
  apply nodeValid_prime [2, 103, 137] ⟨451553, 3, [(2, 5), (103, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_137
  · decide +kernel

theorem prime_610829 : Nat.Prime 610829 := by
  apply nodeValid_prime [2, 79, 1933] ⟨610829, 2, [(2, 2), (79, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1933
  · decide +kernel

theorem prime_805241 : Nat.Prime 805241 := by
  apply nodeValid_prime [2, 5, 41, 491] ⟨805241, 3, [(2, 3), (5, 1), (41, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_491
  · decide +kernel

theorem prime_956513 : Nat.Prime 956513 := by
  apply nodeValid_prime [2, 71, 421] ⟨956513, 3, [(2, 5), (71, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_421
  · decide +kernel

theorem prime_1106419 : Nat.Prime 1106419 := by
  apply nodeValid_prime [2, 3, 61, 3023] ⟨1106419, 3, [(2, 1), (3, 1), (61, 1), (3023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_3023
  · decide +kernel

theorem prime_1221659 : Nat.Prime 1221659 := by
  apply nodeValid_prime [2, 610829] ⟨1221659, 2, [(2, 1), (610829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_610829
  · decide +kernel

theorem prime_1556519 : Nat.Prime 1556519 := by
  apply nodeValid_prime [2, 19, 40961] ⟨1556519, 19, [(2, 1), (19, 1), (40961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_40961
  · decide +kernel

theorem prime_1640531 : Nat.Prime 1640531 := by
  apply nodeValid_prime [2, 5, 29, 5657] ⟨1640531, 2, [(2, 1), (5, 1), (29, 1), (5657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_5657
  · decide +kernel

theorem prime_1699279 : Nat.Prime 1699279 := by
  apply nodeValid_prime [2, 3, 7, 40459] ⟨1699279, 3, [(2, 1), (3, 1), (7, 1), (40459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_40459
  · decide +kernel

theorem prime_1703203 : Nat.Prime 1703203 := by
  apply nodeValid_prime [2, 3, 31, 9157] ⟨1703203, 3, [(2, 1), (3, 1), (31, 1), (9157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_9157
  · decide +kernel

theorem prime_2041661 : Nat.Prime 2041661 := by
  apply nodeValid_prime [2, 5, 31, 37, 89] ⟨2041661, 3, [(2, 2), (5, 1), (31, 1), (37, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_37
    · exact prime_89
  · decide +kernel

theorem prime_2485907 : Nat.Prime 2485907 := by
  apply nodeValid_prime [2, 59, 21067] ⟨2485907, 2, [(2, 1), (59, 1), (21067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_21067
  · decide +kernel

theorem prime_2643943 : Nat.Prime 2643943 := by
  apply nodeValid_prime [2, 3, 7, 17, 23] ⟨2643943, 5, [(2, 1), (3, 1), (7, 2), (17, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_2688863 : Nat.Prime 2688863 := by
  apply nodeValid_prime [2, 11, 41, 271] ⟨2688863, 5, [(2, 1), (11, 2), (41, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_271
  · decide +kernel

theorem prime_2789273 : Nat.Prime 2789273 := by
  apply nodeValid_prime [2, 151, 2309] ⟨2789273, 3, [(2, 3), (151, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_2309
  · decide +kernel

theorem prime_3187159 : Nat.Prime 3187159 := by
  apply nodeValid_prime [2, 3, 13, 29, 1409] ⟨3187159, 6, [(2, 1), (3, 1), (13, 1), (29, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_1409
  · decide +kernel

theorem prime_3281063 : Nat.Prime 3281063 := by
  apply nodeValid_prime [2, 1640531] ⟨3281063, 5, [(2, 1), (1640531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1640531
  · decide +kernel

theorem prime_3392999 : Nat.Prime 3392999 := by
  apply nodeValid_prime [2, 7, 242357] ⟨3392999, 7, [(2, 1), (7, 1), (242357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_242357
  · decide +kernel

theorem prime_3899209 : Nat.Prime 3899209 := by
  apply nodeValid_prime [2, 3, 37, 4391] ⟨3899209, 11, [(2, 3), (3, 1), (37, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4391
  · decide +kernel

theorem prime_3939539 : Nat.Prime 3939539 := by
  apply nodeValid_prime [2, 37, 139, 383] ⟨3939539, 2, [(2, 1), (37, 1), (139, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_139
    · exact prime_383
  · decide +kernel

theorem prime_4320857 : Nat.Prime 4320857 := by
  apply nodeValid_prime [2, 17, 31771] ⟨4320857, 3, [(2, 3), (17, 1), (31771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31771
  · decide +kernel

theorem prime_4432391 : Nat.Prime 4432391 := by
  apply nodeValid_prime [2, 5, 53, 8363] ⟨4432391, 13, [(2, 1), (5, 1), (53, 1), (8363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_8363
  · decide +kernel

theorem prime_4800931 : Nat.Prime 4800931 := by
  apply nodeValid_prime [2, 3, 5, 160031] ⟨4800931, 2, [(2, 1), (3, 1), (5, 1), (160031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_160031
  · decide +kernel

theorem prime_5309779 : Nat.Prime 5309779 := by
  apply nodeValid_prime [2, 3, 19, 47, 991] ⟨5309779, 19, [(2, 1), (3, 1), (19, 1), (47, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_47
    · exact prime_991
  · decide +kernel

theorem prime_5466701 : Nat.Prime 5466701 := by
  apply nodeValid_prime [2, 5, 54667] ⟨5466701, 2, [(2, 2), (5, 2), (54667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_54667
  · decide +kernel

theorem prime_6191821 : Nat.Prime 6191821 := by
  apply nodeValid_prime [2, 3, 5, 41, 839] ⟨6191821, 6, [(2, 2), (3, 2), (5, 1), (41, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_839
  · decide +kernel

theorem prime_9792701 : Nat.Prime 9792701 := by
  apply nodeValid_prime [2, 5, 97927] ⟨9792701, 2, [(2, 2), (5, 2), (97927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97927
  · decide +kernel

theorem prime_9801997 : Nat.Prime 9801997 := by
  apply nodeValid_prime [2, 3, 17, 48049] ⟨9801997, 5, [(2, 2), (3, 1), (17, 1), (48049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_48049
  · decide +kernel

theorem prime_10733963 : Nat.Prime 10733963 := by
  apply nodeValid_prime [2, 23, 233347] ⟨10733963, 2, [(2, 1), (23, 1), (233347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_233347
  · decide +kernel

theorem prime_13875331 : Nat.Prime 13875331 := by
  apply nodeValid_prime [2, 3, 5, 7, 9439] ⟨13875331, 3, [(2, 1), (3, 1), (5, 1), (7, 2), (9439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_9439
  · decide +kernel

theorem prime_14478227 : Nat.Prime 14478227 := by
  apply nodeValid_prime [2, 7, 157, 941] ⟨14478227, 2, [(2, 1), (7, 2), (157, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_157
    · exact prime_941
  · decide +kernel

theorem prime_14754401 : Nat.Prime 14754401 := by
  apply nodeValid_prime [2, 5, 18443] ⟨14754401, 3, [(2, 5), (5, 2), (18443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18443
  · decide +kernel

theorem prime_15544843 : Nat.Prime 15544843 := by
  apply nodeValid_prime [2, 3, 137, 18911] ⟨15544843, 2, [(2, 1), (3, 1), (137, 1), (18911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_18911
  · decide +kernel

theorem prime_19927091 : Nat.Prime 19927091 := by
  apply nodeValid_prime [2, 5, 37, 53857] ⟨19927091, 6, [(2, 1), (5, 1), (37, 1), (53857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_53857
  · decide +kernel

theorem prime_20820769 : Nat.Prime 20820769 := by
  apply nodeValid_prime [2, 3, 73, 2971] ⟨20820769, 11, [(2, 5), (3, 1), (73, 1), (2971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_2971
  · decide +kernel

theorem prime_21331333 : Nat.Prime 21331333 := by
  apply nodeValid_prime [2, 3, 11, 59, 83] ⟨21331333, 2, [(2, 2), (3, 2), (11, 2), (59, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_83
  · decide +kernel

theorem prime_23723569 : Nat.Prime 23723569 := by
  apply nodeValid_prime [2, 3, 11, 17, 881] ⟨23723569, 29, [(2, 4), (3, 2), (11, 1), (17, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_881
  · decide +kernel

theorem prime_27251249 : Nat.Prime 27251249 := by
  apply nodeValid_prime [2, 1703203] ⟨27251249, 3, [(2, 4), (1703203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1703203
  · decide +kernel

theorem prime_27264049 : Nat.Prime 27264049 := by
  apply nodeValid_prime [2, 3, 7, 53, 1531] ⟨27264049, 11, [(2, 4), (3, 1), (7, 1), (53, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_1531
  · decide +kernel

theorem prime_28805587 : Nat.Prime 28805587 := by
  apply nodeValid_prime [2, 3, 4800931] ⟨28805587, 2, [(2, 1), (3, 1), (4800931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4800931
  · decide +kernel

theorem prime_29508803 : Nat.Prime 29508803 := by
  apply nodeValid_prime [2, 14754401] ⟨29508803, 2, [(2, 1), (14754401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14754401
  · decide +kernel

theorem prime_43733609 : Nat.Prime 43733609 := by
  apply nodeValid_prime [2, 5466701] ⟨43733609, 3, [(2, 3), (5466701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5466701
  · decide +kernel

theorem prime_45281129 : Nat.Prime 45281129 := by
  apply nodeValid_prime [2, 101, 56041] ⟨45281129, 3, [(2, 3), (101, 1), (56041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_56041
  · decide +kernel

theorem prime_58756207 : Nat.Prime 58756207 := by
  apply nodeValid_prime [2, 3, 9792701] ⟨58756207, 3, [(2, 1), (3, 1), (9792701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9792701
  · decide +kernel

theorem prime_58811983 : Nat.Prime 58811983 := by
  apply nodeValid_prime [2, 3, 9801997] ⟨58811983, 3, [(2, 1), (3, 1), (9801997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9801997
  · decide +kernel

theorem prime_59134573 : Nat.Prime 59134573 := by
  apply nodeValid_prime [2, 3, 7, 4789] ⟨59134573, 22, [(2, 2), (3, 2), (7, 3), (4789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4789
  · decide +kernel

theorem prime_90562259 : Nat.Prime 90562259 := by
  apply nodeValid_prime [2, 45281129] ⟨90562259, 2, [(2, 1), (45281129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45281129
  · decide +kernel

theorem prime_97078259 : Nat.Prime 97078259 := by
  apply nodeValid_prime [2, 19, 173, 14767] ⟨97078259, 6, [(2, 1), (19, 1), (173, 1), (14767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_173
    · exact prime_14767
  · decide +kernel

theorem prime_110244107 : Nat.Prime 110244107 := by
  apply nodeValid_prime [2, 7, 23, 342373] ⟨110244107, 2, [(2, 1), (7, 1), (23, 1), (342373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_342373
  · decide +kernel

theorem prime_129469757 : Nat.Prime 129469757 := by
  apply nodeValid_prime [2, 13, 17, 167, 877] ⟨129469757, 2, [(2, 2), (13, 1), (17, 1), (167, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_167
    · exact prime_877
  · decide +kernel

theorem prime_134999099 : Nat.Prime 134999099 := by
  apply nodeValid_prime [2, 13, 23, 225751] ⟨134999099, 6, [(2, 1), (13, 1), (23, 1), (225751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_225751
  · decide +kernel

theorem prime_148072679 : Nat.Prime 148072679 := by
  apply nodeValid_prime [2, 13, 31, 183713] ⟨148072679, 19, [(2, 1), (13, 1), (31, 1), (183713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_183713
  · decide +kernel

theorem prime_155448431 : Nat.Prime 155448431 := by
  apply nodeValid_prime [2, 5, 15544843] ⟨155448431, 17, [(2, 1), (5, 1), (15544843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15544843
  · decide +kernel

theorem prime_178647559 : Nat.Prime 178647559 := by
  apply nodeValid_prime [2, 3, 1759, 16927] ⟨178647559, 3, [(2, 1), (3, 1), (1759, 1), (16927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1759
    · exact prime_16927
  · decide +kernel

theorem prime_192356609 : Nat.Prime 192356609 := by
  apply nodeValid_prime [2, 19, 71, 557] ⟨192356609, 3, [(2, 8), (19, 1), (71, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71
    · exact prime_557
  · decide +kernel

theorem prime_194156519 : Nat.Prime 194156519 := by
  apply nodeValid_prime [2, 97078259] ⟨194156519, 7, [(2, 1), (97078259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_97078259
  · decide +kernel

theorem prime_338035349 : Nat.Prime 338035349 := by
  apply nodeValid_prime [2, 7, 2687, 4493] ⟨338035349, 2, [(2, 2), (7, 1), (2687, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2687
    · exact prime_4493
  · decide +kernel

theorem prime_383743879 : Nat.Prime 383743879 := by
  apply nodeValid_prime [2, 3, 7, 2039, 4481] ⟨383743879, 6, [(2, 1), (3, 1), (7, 1), (2039, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2039
    · exact prime_4481
  · decide +kernel

theorem prime_881952857 : Nat.Prime 881952857 := by
  apply nodeValid_prime [2, 110244107] ⟨881952857, 3, [(2, 3), (110244107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_110244107
  · decide +kernel

theorem prime_1043087431 : Nat.Prime 1043087431 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 451553] ⟨1043087431, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (451553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_451553
  · decide +kernel

theorem prime_1853213057 : Nat.Prime 1853213057 := by
  apply nodeValid_prime [2, 14478227] ⟨1853213057, 3, [(2, 7), (14478227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14478227
  · decide +kernel

theorem prime_2149820921 : Nat.Prime 2149820921 := by
  apply nodeValid_prime [2, 5, 13, 1931, 2141] ⟨2149820921, 3, [(2, 3), (5, 1), (13, 1), (1931, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1931
    · exact prime_2141
  · decide +kernel

theorem prime_2395397713 : Nat.Prime 2395397713 := by
  apply nodeValid_prime [2, 3, 2477, 20147] ⟨2395397713, 5, [(2, 4), (3, 1), (2477, 1), (20147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2477
    · exact prime_20147
  · decide +kernel

theorem prime_2704282793 : Nat.Prime 2704282793 := by
  apply nodeValid_prime [2, 338035349] ⟨2704282793, 3, [(2, 3), (338035349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_338035349
  · decide +kernel

theorem prime_3593938181 : Nat.Prime 3593938181 := by
  apply nodeValid_prime [2, 5, 7, 83, 309289] ⟨3593938181, 3, [(2, 2), (5, 1), (7, 1), (83, 1), (309289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_83
    · exact prime_309289
  · decide +kernel

theorem prime_5408565587 : Nat.Prime 5408565587 := by
  apply nodeValid_prime [2, 2704282793] ⟨5408565587, 2, [(2, 1), (2704282793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2704282793
  · decide +kernel

theorem prime_6611618509 : Nat.Prime 6611618509 := by
  apply nodeValid_prime [2, 3, 11, 41, 1221659] ⟨6611618509, 2, [(2, 2), (3, 1), (11, 1), (41, 1), (1221659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_1221659
  · decide +kernel

theorem prime_7452267629 : Nat.Prime 7452267629 := by
  apply nodeValid_prime [2, 13, 17, 19, 23, 101, 191] ⟨7452267629, 3, [(2, 2), (13, 1), (17, 1), (19, 1), (23, 1), (101, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_23
    · exact prime_101
    · exact prime_191
  · decide +kernel

theorem prime_7674963739 : Nat.Prime 7674963739 := by
  apply nodeValid_prime [2, 3, 13, 29, 3392999] ⟨7674963739, 2, [(2, 1), (3, 1), (13, 1), (29, 1), (3392999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_3392999
  · decide +kernel

theorem prime_7739354717 : Nat.Prime 7739354717 := by
  apply nodeValid_prime [2, 71, 27251249] ⟨7739354717, 2, [(2, 2), (71, 1), (27251249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_27251249
  · decide +kernel

theorem prime_9529640651 : Nat.Prime 9529640651 := by
  apply nodeValid_prime [2, 5, 43, 4432391] ⟨9529640651, 2, [(2, 1), (5, 2), (43, 1), (4432391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_4432391
  · decide +kernel

theorem prime_9577660361 : Nat.Prime 9577660361 := by
  apply nodeValid_prime [2, 5, 12329, 19421] ⟨9577660361, 3, [(2, 3), (5, 1), (12329, 1), (19421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12329
    · exact prime_19421
  · decide +kernel

theorem prime_18995433857 : Nat.Prime 18995433857 := by
  apply nodeValid_prime [2, 7, 2927, 7243] ⟨18995433857, 3, [(2, 7), (7, 1), (2927, 1), (7243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2927
    · exact prime_7243
  · decide +kernel

theorem prime_19316121109 : Nat.Prime 19316121109 := by
  apply nodeValid_prime [2, 3, 1999, 805241] ⟨19316121109, 2, [(2, 2), (3, 1), (1999, 1), (805241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1999
    · exact prime_805241
  · decide +kernel

theorem prime_22947923483 : Nat.Prime 22947923483 := by
  apply nodeValid_prime [2, 11, 1043087431] ⟨22947923483, 2, [(2, 1), (11, 1), (1043087431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1043087431
  · decide +kernel

theorem prime_23373395093 : Nat.Prime 23373395093 := by
  apply nodeValid_prime [2, 97, 523, 115183] ⟨23373395093, 2, [(2, 2), (97, 1), (523, 1), (115183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_523
    · exact prime_115183
  · decide +kernel

theorem prime_25540427657 : Nat.Prime 25540427657 := by
  apply nodeValid_prime [2, 73, 43733609] ⟨25540427657, 3, [(2, 3), (73, 1), (43733609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_43733609
  · decide +kernel

theorem prime_28877535901 : Nat.Prime 28877535901 := by
  apply nodeValid_prime [2, 3, 5, 29, 1106419] ⟨28877535901, 14, [(2, 2), (3, 2), (5, 2), (29, 1), (1106419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1106419
  · decide +kernel

theorem prime_37482996361 : Nat.Prime 37482996361 := by
  apply nodeValid_prime [2, 3, 5, 167, 739, 2531] ⟨37482996361, 7, [(2, 3), (3, 1), (5, 1), (167, 1), (739, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_739
    · exact prime_2531
  · decide +kernel

theorem prime_74965997593 : Nat.Prime 74965997593 := by
  apply nodeValid_prime [2, 3, 97, 10733963] ⟨74965997593, 10, [(2, 3), (3, 2), (97, 1), (10733963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_10733963
  · decide +kernel

theorem prime_114164033173 : Nat.Prime 114164033173 := by
  apply nodeValid_prime [2, 3, 7, 194156519] ⟨114164033173, 2, [(2, 2), (3, 1), (7, 2), (194156519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_194156519
  · decide +kernel

theorem prime_115124453803 : Nat.Prime 115124453803 := by
  apply nodeValid_prime [2, 3, 2293, 2789273] ⟨115124453803, 2, [(2, 1), (3, 2), (2293, 1), (2789273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2293
    · exact prime_2789273
  · decide +kernel

theorem prime_233345025059 : Nat.Prime 233345025059 := by
  apply nodeValid_prime [2, 1973, 59134573] ⟨233345025059, 2, [(2, 1), (1973, 1), (59134573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1973
    · exact prime_59134573
  · decide +kernel

theorem prime_449795956333 : Nat.Prime 449795956333 := by
  apply nodeValid_prime [2, 3, 37482996361] ⟨449795956333, 2, [(2, 2), (3, 1), (37482996361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37482996361
  · decide +kernel

theorem prime_449795957071 : Nat.Prime 449795957071 := by
  apply nodeValid_prime [2, 3, 5, 17, 881952857] ⟨449795957071, 6, [(2, 1), (3, 1), (5, 1), (17, 1), (881952857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_881952857
  · decide +kernel

theorem prime_449795985559 : Nat.Prime 449795985559 := by
  apply nodeValid_prime [2, 3, 74965997593] ⟨449795985559, 15, [(2, 1), (3, 1), (74965997593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74965997593
  · decide +kernel

theorem prime_450554751403 : Nat.Prime 450554751403 := by
  apply nodeValid_prime [2, 3, 7, 29, 449, 28409] ⟨450554751403, 3, [(2, 1), (3, 1), (7, 1), (29, 2), (449, 1), (28409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_449
    · exact prime_28409
  · decide +kernel

theorem prime_450554753377 : Nat.Prime 450554753377 := by
  apply nodeValid_prime [2, 3, 7, 13, 409, 14011] ⟨450554753377, 5, [(2, 5), (3, 3), (7, 1), (13, 1), (409, 1), (14011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_409
    · exact prime_14011
  · decide +kernel

theorem prime_450554754361 : Nat.Prime 450554754361 := by
  apply nodeValid_prime [2, 3, 5, 29, 129469757] ⟨450554754361, 14, [(2, 3), (3, 1), (5, 1), (29, 1), (129469757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_129469757
  · decide +kernel

theorem prime_451314384751 : Nat.Prime 451314384751 := by
  apply nodeValid_prime [2, 3, 5, 53, 691, 5477] ⟨451314384751, 12, [(2, 1), (3, 2), (5, 3), (53, 1), (691, 1), (5477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_691
    · exact prime_5477
  · decide +kernel

theorem prime_451314390521 : Nat.Prime 451314390521 := by
  apply nodeValid_prime [2, 5, 7, 5347, 301447] ⟨451314390521, 12, [(2, 3), (5, 1), (7, 1), (5347, 1), (301447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_5347
    · exact prime_301447
  · decide +kernel

theorem prime_451314393377 : Nat.Prime 451314393377 := by
  apply nodeValid_prime [2, 7, 11, 1201, 21787] ⟨451314393377, 3, [(2, 5), (7, 2), (11, 1), (1201, 1), (21787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1201
    · exact prime_21787
  · decide +kernel

theorem prime_452074861961 : Nat.Prime 452074861961 := by
  apply nodeValid_prime [2, 5, 383, 29508803] ⟨452074861961, 6, [(2, 3), (5, 1), (383, 1), (29508803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_383
    · exact prime_29508803
  · decide +kernel

theorem prime_452074862801 : Nat.Prime 452074862801 := by
  apply nodeValid_prime [2, 5, 11, 4363, 23549] ⟨452074862801, 3, [(2, 4), (5, 2), (11, 1), (4363, 1), (23549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_4363
    · exact prime_23549
  · decide +kernel

theorem prime_452074882379 : Nat.Prime 452074882379 := by
  apply nodeValid_prime [2, 7, 19, 59, 28805587] ⟨452074882379, 2, [(2, 1), (7, 1), (19, 1), (59, 1), (28805587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_59
    · exact prime_28805587
  · decide +kernel

theorem prime_452836210513 : Nat.Prime 452836210513 := by
  apply nodeValid_prime [2, 3, 7, 1409, 956513] ⟨452836210513, 10, [(2, 4), (3, 1), (7, 1), (1409, 1), (956513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1409
    · exact prime_956513
  · decide +kernel

theorem prime_452836210807 : Nat.Prime 452836210807 := by
  apply nodeValid_prime [2, 3, 7, 3593938181] ⟨452836210807, 3, [(2, 1), (3, 2), (7, 1), (3593938181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3593938181
  · decide +kernel

theorem prime_452836245899 : Nat.Prime 452836245899 := by
  apply nodeValid_prime [2, 29, 43, 4073, 44579] ⟨452836245899, 2, [(2, 1), (29, 1), (43, 1), (4073, 1), (44579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_43
    · exact prime_4073
    · exact prime_44579
  · decide +kernel

theorem prime_453598478477 : Nat.Prime 453598478477 := by
  apply nodeValid_prime [2, 11, 13, 29, 2485907] ⟨453598478477, 3, [(2, 2), (11, 2), (13, 1), (29, 1), (2485907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_29
    · exact prime_2485907
  · decide +kernel

theorem prime_453598520461 : Nat.Prime 453598520461 := by
  apply nodeValid_prime [2, 3, 5, 19, 101, 3939539] ⟨453598520461, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (101, 1), (3939539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_101
    · exact prime_3939539
  · decide +kernel

theorem prime_453598521659 : Nat.Prime 453598521659 := by
  apply nodeValid_prime [2, 1459, 155448431] ⟨453598521659, 2, [(2, 1), (1459, 1), (155448431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1459
    · exact prime_155448431
  · decide +kernel

theorem prime_454361588927 : Nat.Prime 454361588927 := by
  apply nodeValid_prime [2, 7, 2339, 13875331] ⟨454361588927, 5, [(2, 1), (7, 1), (2339, 1), (13875331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2339
    · exact prime_13875331
  · decide +kernel

theorem prime_454361604241 : Nat.Prime 454361604241 := by
  apply nodeValid_prime [2, 3, 5, 577, 3281063] ⟨454361604241, 7, [(2, 4), (3, 1), (5, 1), (577, 1), (3281063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_577
    · exact prime_3281063
  · decide +kernel

theorem prime_454361604551 : Nat.Prime 454361604551 := by
  apply nodeValid_prime [2, 5, 7, 491, 2643943] ⟨454361604551, 7, [(2, 1), (5, 2), (7, 1), (491, 1), (2643943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_491
    · exact prime_2643943
  · decide +kernel

theorem prime_455125565471 : Nat.Prime 455125565471 := by
  apply nodeValid_prime [2, 5, 19, 2395397713] ⟨455125565471, 11, [(2, 1), (5, 1), (19, 1), (2395397713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_2395397713
  · decide +kernel

theorem prime_455125579151 : Nat.Prime 455125579151 := by
  apply nodeValid_prime [2, 5, 11, 19, 547, 79621] ⟨455125579151, 22, [(2, 1), (5, 2), (11, 1), (19, 1), (547, 1), (79621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_547
    · exact prime_79621
  · decide +kernel

theorem prime_455125579423 : Nat.Prime 455125579423 := by
  apply nodeValid_prime [2, 3, 1291, 58756207] ⟨455125579423, 6, [(2, 1), (3, 1), (1291, 1), (58756207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1291
    · exact prime_58756207
  · decide +kernel

theorem prime_455890411807 : Nat.Prime 455890411807 := by
  apply nodeValid_prime [2, 3, 839, 90562259] ⟨455890411807, 3, [(2, 1), (3, 1), (839, 1), (90562259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_839
    · exact prime_90562259
  · decide +kernel

theorem prime_455890412023 : Nat.Prime 455890412023 := by
  apply nodeValid_prime [2, 3, 41, 1853213057] ⟨455890412023, 5, [(2, 1), (3, 1), (41, 1), (1853213057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1853213057
  · decide +kernel

theorem prime_455890412569 : Nat.Prime 455890412569 := by
  apply nodeValid_prime [2, 3, 18995433857] ⟨455890412569, 17, [(2, 3), (3, 1), (18995433857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18995433857
  · decide +kernel

theorem prime_456656132693 : Nat.Prime 456656132693 := by
  apply nodeValid_prime [2, 114164033173] ⟨456656132693, 2, [(2, 2), (114164033173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_114164033173
  · decide +kernel

theorem prime_456656141521 : Nat.Prime 456656141521 := by
  apply nodeValid_prime [2, 3, 5, 199, 3187159] ⟨456656141521, 13, [(2, 4), (3, 2), (5, 1), (199, 1), (3187159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_3187159
  · decide +kernel

theorem prime_456656142037 : Nat.Prime 456656142037 := by
  apply nodeValid_prime [2, 3, 257, 148072679] ⟨456656142037, 2, [(2, 2), (3, 1), (257, 1), (148072679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_148072679
  · decide +kernel

theorem prime_457422726307 : Nat.Prime 457422726307 := by
  apply nodeValid_prime [2, 3, 7, 13, 23, 601, 60607] ⟨457422726307, 5, [(2, 1), (3, 1), (7, 1), (13, 1), (23, 1), (601, 1), (60607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_601
    · exact prime_60607
  · decide +kernel

theorem prime_457422751249 : Nat.Prime 457422751249 := by
  apply nodeValid_prime [2, 3, 9529640651] ⟨457422751249, 17, [(2, 4), (3, 1), (9529640651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9529640651
  · decide +kernel

theorem prime_457422752497 : Nat.Prime 457422752497 := by
  apply nodeValid_prime [2, 3, 79, 137, 6427] ⟨457422752497, 5, [(2, 4), (3, 1), (79, 1), (137, 2), (6427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_137
    · exact prime_6427
  · decide +kernel

theorem prime_458190188947 : Nat.Prime 458190188947 := by
  apply nodeValid_prime [2, 3, 7, 173, 2647] ⟨458190188947, 3, [(2, 1), (3, 3), (7, 1), (173, 1), (2647, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173
    · exact prime_2647
  · decide +kernel

theorem prime_458190191003 : Nat.Prime 458190191003 := by
  apply nodeValid_prime [2, 31, 4349, 1699279] ⟨458190191003, 2, [(2, 1), (31, 1), (4349, 1), (1699279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_4349
    · exact prime_1699279
  · decide +kernel

theorem prime_458190191527 : Nat.Prime 458190191527 := by
  apply nodeValid_prime [2, 3, 199, 383743879] ⟨458190191527, 19, [(2, 1), (3, 1), (199, 1), (383743879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_383743879
  · decide +kernel

theorem prime_458958469253 : Nat.Prime 458958469253 := by
  apply nodeValid_prime [2, 19, 61, 2347, 42181] ⟨458958469253, 2, [(2, 2), (19, 1), (61, 1), (2347, 1), (42181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
    · exact prime_2347
    · exact prime_42181
  · decide +kernel

theorem prime_458958469661 : Nat.Prime 458958469661 := by
  apply nodeValid_prime [2, 5, 22947923483] ⟨458958469661, 7, [(2, 2), (5, 1), (22947923483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22947923483
  · decide +kernel

theorem prime_458958524597 : Nat.Prime 458958524597 := by
  apply nodeValid_prime [2, 11, 13, 41, 59, 331697] ⟨458958524597, 3, [(2, 2), (11, 1), (13, 1), (41, 1), (59, 1), (331697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_41
    · exact prime_59
    · exact prime_331697
  · decide +kernel

theorem prime_459727697329 : Nat.Prime 459727697329 := by
  apply nodeValid_prime [2, 3, 9577660361] ⟨459727697329, 7, [(2, 4), (3, 1), (9577660361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9577660361
  · decide +kernel

theorem prime_459727697827 : Nat.Prime 459727697827 := by
  apply nodeValid_prime [2, 3, 25540427657] ⟨459727697827, 2, [(2, 1), (3, 2), (25540427657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25540427657
  · decide +kernel

theorem prime_459727732813 : Nat.Prime 459727732813 := by
  apply nodeValid_prime [2, 3, 41, 12743, 73327] ⟨459727732813, 5, [(2, 2), (3, 1), (41, 1), (12743, 1), (73327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_12743
    · exact prime_73327
  · decide +kernel

theorem prime_460497815213 : Nat.Prime 460497815213 := by
  apply nodeValid_prime [2, 115124453803] ⟨460497815213, 2, [(2, 2), (115124453803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115124453803
  · decide +kernel

theorem prime_460497824341 : Nat.Prime 460497824341 := by
  apply nodeValid_prime [2, 3, 5, 7674963739] ⟨460497824341, 22, [(2, 2), (3, 1), (5, 1), (7674963739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7674963739
  · decide +kernel

theorem prime_460497826891 : Nat.Prime 460497826891 := by
  apply nodeValid_prime [2, 3, 5, 29, 58811983] ⟨460497826891, 11, [(2, 1), (3, 3), (5, 1), (29, 1), (58811983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_58811983
  · decide +kernel

theorem prime_461268744731 : Nat.Prime 461268744731 := by
  apply nodeValid_prime [2, 5, 43, 79, 439, 30931] ⟨461268744731, 2, [(2, 1), (5, 1), (43, 1), (79, 1), (439, 1), (30931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_79
    · exact prime_439
    · exact prime_30931
  · decide +kernel

theorem prime_461268744793 : Nat.Prime 461268744793 := by
  apply nodeValid_prime [2, 3, 17, 53, 21331333] ⟨461268744793, 10, [(2, 3), (3, 1), (17, 1), (53, 1), (21331333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_53
    · exact prime_21331333
  · decide +kernel

theorem prime_461268768179 : Nat.Prime 461268768179 := by
  apply nodeValid_prime [2, 53377, 4320857] ⟨461268768179, 2, [(2, 1), (53377, 1), (4320857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53377
    · exact prime_4320857
  · decide +kernel

theorem prime_462040574417 : Nat.Prime 462040574417 := by
  apply nodeValid_prime [2, 28877535901] ⟨462040574417, 3, [(2, 4), (28877535901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28877535901
  · decide +kernel

theorem prime_462040574819 : Nat.Prime 462040574819 := by
  apply nodeValid_prime [2, 1201, 192356609] ⟨462040574819, 2, [(2, 1), (1201, 1), (192356609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1201
    · exact prime_192356609
  · decide +kernel

theorem prime_462040592999 : Nat.Prime 462040592999 := by
  apply nodeValid_prime [2, 31, 7452267629] ⟨462040592999, 13, [(2, 1), (31, 1), (7452267629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_7452267629
  · decide +kernel

theorem prime_462813293183 : Nat.Prime 462813293183 := by
  apply nodeValid_prime [2, 19, 41, 1301, 5569] ⟨462813293183, 5, [(2, 1), (19, 1), (41, 2), (1301, 1), (5569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_1301
    · exact prime_5569
  · decide +kernel

theorem prime_462813295631 : Nat.Prime 462813295631 := by
  apply nodeValid_prime [2, 5, 7, 6611618509] ⟨462813295631, 7, [(2, 1), (5, 1), (7, 1), (6611618509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6611618509
  · decide +kernel

theorem prime_462813296521 : Nat.Prime 462813296521 := by
  apply nodeValid_prime [2, 3, 5, 17, 23, 1021, 9661] ⟨462813296521, 19, [(2, 3), (3, 1), (5, 1), (17, 1), (23, 1), (1021, 1), (9661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_1021
    · exact prime_9661
  · decide +kernel

theorem prime_463586869831 : Nat.Prime 463586869831 := by
  apply nodeValid_prime [2, 3, 5, 7, 821, 2688863] ⟨463586869831, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (821, 1), (2688863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_821
    · exact prime_2688863
  · decide +kernel

theorem prime_463586905967 : Nat.Prime 463586905967 := by
  apply nodeValid_prime [2, 17, 101, 134999099] ⟨463586905967, 5, [(2, 1), (17, 1), (101, 1), (134999099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_101
    · exact prime_134999099
  · decide +kernel

theorem prime_463586906617 : Nat.Prime 463586906617 := by
  apply nodeValid_prime [2, 3, 19316121109] ⟨463586906617, 5, [(2, 3), (3, 1), (19316121109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19316121109
  · decide +kernel

theorem prime_464361282569 : Nat.Prime 464361282569 := by
  apply nodeValid_prime [2, 2129, 27264049] ⟨464361282569, 3, [(2, 3), (2129, 1), (27264049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2129
    · exact prime_27264049
  · decide +kernel

theorem prime_464361283021 : Nat.Prime 464361283021 := by
  apply nodeValid_prime [2, 3, 5, 7739354717] ⟨464361283021, 2, [(2, 2), (3, 1), (5, 1), (7739354717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7739354717
  · decide +kernel

theorem prime_464361318937 : Nat.Prime 464361318937 := by
  apply nodeValid_prime [2, 3, 2149820921] ⟨464361318937, 19, [(2, 3), (3, 3), (2149820921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2149820921
  · decide +kernel

theorem prime_465136640401 : Nat.Prime 465136640401 := by
  apply nodeValid_prime [2, 3, 5, 73, 5309779] ⟨465136640401, 29, [(2, 4), (3, 1), (5, 2), (73, 1), (5309779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_5309779
  · decide +kernel

theorem prime_465136640483 : Nat.Prime 465136640483 := by
  apply nodeValid_prime [2, 43, 5408565587] ⟨465136640483, 2, [(2, 1), (43, 1), (5408565587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_5408565587
  · decide +kernel

theorem prime_465136641611 : Nat.Prime 465136641611 := by
  apply nodeValid_prime [2, 5, 79, 151, 3899209] ⟨465136641611, 6, [(2, 1), (5, 1), (79, 1), (151, 1), (3899209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_151
    · exact prime_3899209
  · decide +kernel

theorem prime_465912832271 : Nat.Prime 465912832271 := by
  apply nodeValid_prime [2, 5, 37, 809, 1556519] ⟨465912832271, 19, [(2, 1), (5, 1), (37, 1), (809, 1), (1556519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_809
    · exact prime_1556519
  · decide +kernel

theorem prime_465912833873 : Nat.Prime 465912833873 := by
  apply nodeValid_prime [2, 163, 178647559] ⟨465912833873, 3, [(2, 4), (163, 1), (178647559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_178647559
  · decide +kernel

theorem prime_465912842561 : Nat.Prime 465912842561 := by
  apply nodeValid_prime [2, 5, 11, 59, 203947] ⟨465912842561, 6, [(2, 6), (5, 1), (11, 2), (59, 1), (203947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_59
    · exact prime_203947
  · decide +kernel

theorem prime_466689932413 : Nat.Prime 466689932413 := by
  apply nodeValid_prime [2, 3, 11, 571, 6191821] ⟨466689932413, 5, [(2, 2), (3, 1), (11, 1), (571, 1), (6191821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_571
    · exact prime_6191821
  · decide +kernel

theorem prime_466690049369 : Nat.Prime 466690049369 := by
  apply nodeValid_prime [2, 2459, 23723569] ⟨466690049369, 3, [(2, 3), (2459, 1), (23723569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2459
    · exact prime_23723569
  · decide +kernel

theorem prime_466690050119 : Nat.Prime 466690050119 := by
  apply nodeValid_prime [2, 233345025059] ⟨466690050119, 13, [(2, 1), (233345025059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_233345025059
  · decide +kernel

theorem prime_467467901861 : Nat.Prime 467467901861 := by
  apply nodeValid_prime [2, 5, 23373395093] ⟨467467901861, 2, [(2, 2), (5, 1), (23373395093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23373395093
  · decide +kernel

theorem prime_467467902607 : Nat.Prime 467467902607 := by
  apply nodeValid_prime [2, 3, 17, 37, 7853, 15773] ⟨467467902607, 5, [(2, 1), (3, 1), (17, 1), (37, 1), (7853, 1), (15773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_7853
    · exact prime_15773
  · decide +kernel

theorem prime_467467905589 : Nat.Prime 467467905589 := by
  apply nodeValid_prime [2, 3, 1871, 20820769] ⟨467467905589, 6, [(2, 2), (3, 1), (1871, 1), (20820769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1871
    · exact prime_20820769
  · decide +kernel

theorem prime_468246750473 : Nat.Prime 468246750473 := by
  apply nodeValid_prime [2, 240631, 243239] ⟨468246750473, 3, [(2, 3), (240631, 1), (243239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_240631
    · exact prime_243239
  · decide +kernel

theorem prime_468246783707 : Nat.Prime 468246783707 := by
  apply nodeValid_prime [2, 13, 8821, 2041661] ⟨468246783707, 2, [(2, 1), (13, 1), (8821, 1), (2041661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_8821
    · exact prime_2041661
  · decide +kernel

theorem prime_468246784319 : Nat.Prime 468246784319 := by
  apply nodeValid_prime [2, 31, 379, 19927091] ⟨468246784319, 13, [(2, 1), (31, 1), (379, 1), (19927091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_379
    · exact prime_19927091
  · decide +kernel

end Sude.Lucas.Generated
