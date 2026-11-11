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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0107

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9341 : Nat.Prime 9341 := by
  apply nodeValid_prime [2, 5, 467] ⟨9341, 2, [(2, 2), (5, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_467
  · decide +kernel

theorem prime_9431 : Nat.Prime 9431 := by
  apply nodeValid_prime [2, 5, 23, 41] ⟨9431, 7, [(2, 1), (5, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_9547 : Nat.Prime 9547 := by
  apply nodeValid_prime [2, 3, 37, 43] ⟨9547, 2, [(2, 1), (3, 1), (37, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_43
  · decide +kernel

theorem prime_15601 : Nat.Prime 15601 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨15601, 23, [(2, 4), (3, 1), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_16493 : Nat.Prime 16493 := by
  apply nodeValid_prime [2, 7, 19, 31] ⟨16493, 2, [(2, 2), (7, 1), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_20747 : Nat.Prime 20747 := by
  apply nodeValid_prime [2, 11, 23, 41] ⟨20747, 5, [(2, 1), (11, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_21943 : Nat.Prime 21943 := by
  apply nodeValid_prime [2, 3, 23, 53] ⟨21943, 5, [(2, 1), (3, 2), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_22307 : Nat.Prime 22307 := by
  apply nodeValid_prime [2, 19, 587] ⟨22307, 2, [(2, 1), (19, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_587
  · decide +kernel

theorem prime_22811 : Nat.Prime 22811 := by
  apply nodeValid_prime [2, 5, 2281] ⟨22811, 6, [(2, 1), (5, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2281
  · decide +kernel

theorem prime_23827 : Nat.Prime 23827 := by
  apply nodeValid_prime [2, 3, 11, 19] ⟨23827, 2, [(2, 1), (3, 1), (11, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_24923 : Nat.Prime 24923 := by
  apply nodeValid_prime [2, 17, 733] ⟨24923, 2, [(2, 1), (17, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_733
  · decide +kernel

theorem prime_40253 : Nat.Prime 40253 := by
  apply nodeValid_prime [2, 29, 347] ⟨40253, 2, [(2, 2), (29, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_347
  · decide +kernel

theorem prime_45007 : Nat.Prime 45007 := by
  apply nodeValid_prime [2, 3, 13, 577] ⟨45007, 3, [(2, 1), (3, 1), (13, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_577
  · decide +kernel

theorem prime_47441 : Nat.Prime 47441 := by
  apply nodeValid_prime [2, 5, 593] ⟨47441, 3, [(2, 4), (5, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_593
  · decide +kernel

theorem prime_48611 : Nat.Prime 48611 := by
  apply nodeValid_prime [2, 5, 4861] ⟨48611, 2, [(2, 1), (5, 1), (4861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4861
  · decide +kernel

theorem prime_49937 : Nat.Prime 49937 := by
  apply nodeValid_prime [2, 3121] ⟨49937, 3, [(2, 4), (3121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3121
  · decide +kernel

theorem prime_51257 : Nat.Prime 51257 := by
  apply nodeValid_prime [2, 43, 149] ⟨51257, 3, [(2, 3), (43, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_149
  · decide +kernel

theorem prime_52369 : Nat.Prime 52369 := by
  apply nodeValid_prime [2, 3, 1091] ⟨52369, 13, [(2, 4), (3, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
  · decide +kernel

theorem prime_52879 : Nat.Prime 52879 := by
  apply nodeValid_prime [2, 3, 7, 1259] ⟨52879, 3, [(2, 1), (3, 1), (7, 1), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1259
  · decide +kernel

theorem prime_56509 : Nat.Prime 56509 := by
  apply nodeValid_prime [2, 3, 17, 277] ⟨56509, 2, [(2, 2), (3, 1), (17, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_277
  · decide +kernel

theorem prime_60089 : Nat.Prime 60089 := by
  apply nodeValid_prime [2, 7, 29, 37] ⟨60089, 3, [(2, 3), (7, 1), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_60337 : Nat.Prime 60337 := by
  apply nodeValid_prime [2, 3, 419] ⟨60337, 5, [(2, 4), (3, 2), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419
  · decide +kernel

theorem prime_74729 : Nat.Prime 74729 := by
  apply nodeValid_prime [2, 9341] ⟨74729, 3, [(2, 3), (9341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9341
  · decide +kernel

theorem prime_75289 : Nat.Prime 75289 := by
  apply nodeValid_prime [2, 3, 3137] ⟨75289, 13, [(2, 3), (3, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3137
  · decide +kernel

theorem prime_77557 : Nat.Prime 77557 := by
  apply nodeValid_prime [2, 3, 23, 281] ⟨77557, 5, [(2, 2), (3, 1), (23, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_281
  · decide +kernel

theorem prime_78277 : Nat.Prime 78277 := by
  apply nodeValid_prime [2, 3, 11, 593] ⟨78277, 6, [(2, 2), (3, 1), (11, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_593
  · decide +kernel

theorem prime_79999 : Nat.Prime 79999 := by
  apply nodeValid_prime [2, 3, 67, 199] ⟨79999, 3, [(2, 1), (3, 1), (67, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_199
  · decide +kernel

theorem prime_85451 : Nat.Prime 85451 := by
  apply nodeValid_prime [2, 5, 1709] ⟨85451, 2, [(2, 1), (5, 2), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1709
  · decide +kernel

theorem prime_87359 : Nat.Prime 87359 := by
  apply nodeValid_prime [2, 31, 1409] ⟨87359, 19, [(2, 1), (31, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1409
  · decide +kernel

theorem prime_92381 : Nat.Prime 92381 := by
  apply nodeValid_prime [2, 5, 31, 149] ⟨92381, 2, [(2, 2), (5, 1), (31, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_149
  · decide +kernel

theorem prime_93607 : Nat.Prime 93607 := by
  apply nodeValid_prime [2, 3, 15601] ⟨93607, 3, [(2, 1), (3, 1), (15601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15601
  · decide +kernel

theorem prime_100313 : Nat.Prime 100313 := by
  apply nodeValid_prime [2, 12539] ⟨100313, 3, [(2, 3), (12539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12539
  · decide +kernel

theorem prime_104233 : Nat.Prime 104233 := by
  apply nodeValid_prime [2, 3, 43, 101] ⟨104233, 7, [(2, 3), (3, 1), (43, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_101
  · decide +kernel

theorem prime_107449 : Nat.Prime 107449 := by
  apply nodeValid_prime [2, 3, 11, 37] ⟨107449, 7, [(2, 3), (3, 1), (11, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_119533 : Nat.Prime 119533 := by
  apply nodeValid_prime [2, 3, 7, 1423] ⟨119533, 2, [(2, 2), (3, 1), (7, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1423
  · decide +kernel

theorem prime_126397 : Nat.Prime 126397 := by
  apply nodeValid_prime [2, 3, 3511] ⟨126397, 5, [(2, 2), (3, 2), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3511
  · decide +kernel

theorem prime_133843 : Nat.Prime 133843 := by
  apply nodeValid_prime [2, 3, 22307] ⟨133843, 2, [(2, 1), (3, 1), (22307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22307
  · decide +kernel

theorem prime_137191 : Nat.Prime 137191 := by
  apply nodeValid_prime [2, 3, 5, 17, 269] ⟨137191, 12, [(2, 1), (3, 1), (5, 1), (17, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_269
  · decide +kernel

theorem prime_152377 : Nat.Prime 152377 := by
  apply nodeValid_prime [2, 3, 7, 907] ⟨152377, 5, [(2, 3), (3, 1), (7, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_907
  · decide +kernel

theorem prime_159563 : Nat.Prime 159563 := by
  apply nodeValid_prime [2, 13, 17, 19] ⟨159563, 2, [(2, 1), (13, 1), (17, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_162251 : Nat.Prime 162251 := by
  apply nodeValid_prime [2, 5, 11, 59] ⟨162251, 2, [(2, 1), (5, 3), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_164023 : Nat.Prime 164023 := by
  apply nodeValid_prime [2, 3, 27337] ⟨164023, 3, [(2, 1), (3, 1), (27337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27337
  · decide +kernel

theorem prime_170341 : Nat.Prime 170341 := by
  apply nodeValid_prime [2, 3, 5, 17, 167] ⟨170341, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_167
  · decide +kernel

theorem prime_186071 : Nat.Prime 186071 := by
  apply nodeValid_prime [2, 5, 23, 809] ⟨186071, 13, [(2, 1), (5, 1), (23, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_809
  · decide +kernel

theorem prime_193243 : Nat.Prime 193243 := by
  apply nodeValid_prime [2, 3, 7, 43, 107] ⟨193243, 2, [(2, 1), (3, 1), (7, 1), (43, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_107
  · decide +kernel

theorem prime_204751 : Nat.Prime 204751 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨204751, 3, [(2, 1), (3, 2), (5, 3), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_216829 : Nat.Prime 216829 := by
  apply nodeValid_prime [2, 3, 19, 317] ⟨216829, 2, [(2, 2), (3, 2), (19, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_317
  · decide +kernel

theorem prime_229213 : Nat.Prime 229213 := by
  apply nodeValid_prime [2, 3, 6367] ⟨229213, 2, [(2, 2), (3, 2), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6367
  · decide +kernel

theorem prime_244381 : Nat.Prime 244381 := by
  apply nodeValid_prime [2, 3, 5, 4073] ⟨244381, 13, [(2, 2), (3, 1), (5, 1), (4073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4073
  · decide +kernel

theorem prime_255499 : Nat.Prime 255499 := by
  apply nodeValid_prime [2, 3, 97, 439] ⟨255499, 2, [(2, 1), (3, 1), (97, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_439
  · decide +kernel

theorem prime_311791 : Nat.Prime 311791 := by
  apply nodeValid_prime [2, 3, 5, 19, 547] ⟨311791, 6, [(2, 1), (3, 1), (5, 1), (19, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_547
  · decide +kernel

theorem prime_319127 : Nat.Prime 319127 := by
  apply nodeValid_prime [2, 159563] ⟨319127, 5, [(2, 1), (159563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_159563
  · decide +kernel

theorem prime_324503 : Nat.Prime 324503 := by
  apply nodeValid_prime [2, 162251] ⟨324503, 5, [(2, 1), (162251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_162251
  · decide +kernel

theorem prime_327319 : Nat.Prime 327319 := by
  apply nodeValid_prime [2, 3, 17, 3209] ⟨327319, 3, [(2, 1), (3, 1), (17, 1), (3209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3209
  · decide +kernel

theorem prime_358073 : Nat.Prime 358073 := by
  apply nodeValid_prime [2, 11, 13, 313] ⟨358073, 3, [(2, 3), (11, 1), (13, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_313
  · decide +kernel

theorem prime_400853 : Nat.Prime 400853 := by
  apply nodeValid_prime [2, 100213] ⟨400853, 2, [(2, 2), (100213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_100213
  · decide +kernel

theorem prime_426871 : Nat.Prime 426871 := by
  apply nodeValid_prime [2, 3, 5, 17, 31] ⟨426871, 3, [(2, 1), (3, 4), (5, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_552103 : Nat.Prime 552103 := by
  apply nodeValid_prime [2, 3, 19, 29, 167] ⟨552103, 3, [(2, 1), (3, 1), (19, 1), (29, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_167
  · decide +kernel

theorem prime_566719 : Nat.Prime 566719 := by
  apply nodeValid_prime [2, 3, 29, 3257] ⟨566719, 3, [(2, 1), (3, 1), (29, 1), (3257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_3257
  · decide +kernel

theorem prime_609509 : Nat.Prime 609509 := by
  apply nodeValid_prime [2, 152377] ⟨609509, 2, [(2, 2), (152377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_152377
  · decide +kernel

theorem prime_624791 : Nat.Prime 624791 := by
  apply nodeValid_prime [2, 5, 43, 1453] ⟨624791, 13, [(2, 1), (5, 1), (43, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_1453
  · decide +kernel

theorem prime_691433 : Nat.Prime 691433 := by
  apply nodeValid_prime [2, 7, 12347] ⟨691433, 3, [(2, 3), (7, 1), (12347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12347
  · decide +kernel

theorem prime_773657 : Nat.Prime 773657 := by
  apply nodeValid_prime [2, 13, 43, 173] ⟨773657, 3, [(2, 3), (13, 1), (43, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_173
  · decide +kernel

theorem prime_810763 : Nat.Prime 810763 := by
  apply nodeValid_prime [2, 3, 163, 829] ⟨810763, 5, [(2, 1), (3, 1), (163, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_829
  · decide +kernel

theorem prime_835327 : Nat.Prime 835327 := by
  apply nodeValid_prime [2, 3, 31, 499] ⟨835327, 3, [(2, 1), (3, 3), (31, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_499
  · decide +kernel

theorem prime_866311 : Nat.Prime 866311 := by
  apply nodeValid_prime [2, 3, 5, 67, 431] ⟨866311, 3, [(2, 1), (3, 1), (5, 1), (67, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_431
  · decide +kernel

theorem prime_929557 : Nat.Prime 929557 := by
  apply nodeValid_prime [2, 3, 19, 151] ⟨929557, 15, [(2, 2), (3, 4), (19, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_151
  · decide +kernel

theorem prime_988271 : Nat.Prime 988271 := by
  apply nodeValid_prime [2, 5, 37, 2671] ⟨988271, 7, [(2, 1), (5, 1), (37, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_2671
  · decide +kernel

theorem prime_1037411 : Nat.Prime 1037411 := by
  apply nodeValid_prime [2, 5, 11, 9431] ⟨1037411, 2, [(2, 1), (5, 1), (11, 1), (9431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_9431
  · decide +kernel

theorem prime_1131913 : Nat.Prime 1131913 := by
  apply nodeValid_prime [2, 3, 79, 199] ⟨1131913, 5, [(2, 3), (3, 2), (79, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_199
  · decide +kernel

theorem prime_1371911 : Nat.Prime 1371911 := by
  apply nodeValid_prime [2, 5, 137191] ⟨1371911, 7, [(2, 1), (5, 1), (137191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137191
  · decide +kernel

theorem prime_1630381 : Nat.Prime 1630381 := by
  apply nodeValid_prime [2, 3, 5, 29, 937] ⟨1630381, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_937
  · decide +kernel

theorem prime_1793497 : Nat.Prime 1793497 := by
  apply nodeValid_prime [2, 3, 74729] ⟨1793497, 7, [(2, 3), (3, 1), (74729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74729
  · decide +kernel

theorem prime_2168291 : Nat.Prime 2168291 := by
  apply nodeValid_prime [2, 5, 216829] ⟨2168291, 2, [(2, 1), (5, 1), (216829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_216829
  · decide +kernel

theorem prime_2224457 : Nat.Prime 2224457 := by
  apply nodeValid_prime [2, 13, 73, 293] ⟨2224457, 3, [(2, 3), (13, 1), (73, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_293
  · decide +kernel

theorem prime_2318917 : Nat.Prime 2318917 := by
  apply nodeValid_prime [2, 3, 193243] ⟨2318917, 2, [(2, 2), (3, 1), (193243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193243
  · decide +kernel

theorem prime_2542147 : Nat.Prime 2542147 := by
  apply nodeValid_prime [2, 3, 17, 24923] ⟨2542147, 2, [(2, 1), (3, 1), (17, 1), (24923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_24923
  · decide +kernel

theorem prime_2743823 : Nat.Prime 2743823 := by
  apply nodeValid_prime [2, 1371911] ⟨2743823, 5, [(2, 1), (1371911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1371911
  · decide +kernel

theorem prime_3037213 : Nat.Prime 3037213 := by
  apply nodeValid_prime [2, 3, 239, 353] ⟨3037213, 5, [(2, 2), (3, 2), (239, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_353
  · decide +kernel

theorem prime_3123217 : Nat.Prime 3123217 := by
  apply nodeValid_prime [2, 3, 23, 41] ⟨3123217, 5, [(2, 4), (3, 2), (23, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_3341309 : Nat.Prime 3341309 := by
  apply nodeValid_prime [2, 835327] ⟨3341309, 2, [(2, 2), (835327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_835327
  · decide +kernel

theorem prime_3420533 : Nat.Prime 3420533 := by
  apply nodeValid_prime [2, 19, 45007] ⟨3420533, 2, [(2, 2), (19, 1), (45007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_45007
  · decide +kernel

theorem prime_3703277 : Nat.Prime 3703277 := by
  apply nodeValid_prime [2, 23, 40253] ⟨3703277, 2, [(2, 2), (23, 1), (40253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_40253
  · decide +kernel

theorem prime_3718229 : Nat.Prime 3718229 := by
  apply nodeValid_prime [2, 929557] ⟨3718229, 2, [(2, 2), (929557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_929557
  · decide +kernel

theorem prime_3822367 : Nat.Prime 3822367 := by
  apply nodeValid_prime [2, 3, 179, 3559] ⟨3822367, 3, [(2, 1), (3, 1), (179, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_3559
  · decide +kernel

theorem prime_3882937 : Nat.Prime 3882937 := by
  apply nodeValid_prime [2, 3, 17, 31, 307] ⟨3882937, 10, [(2, 3), (3, 1), (17, 1), (31, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_307
  · decide +kernel

theorem prime_4336583 : Nat.Prime 4336583 := by
  apply nodeValid_prime [2, 2168291] ⟨4336583, 5, [(2, 1), (2168291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2168291
  · decide +kernel

theorem prime_4467779 : Nat.Prime 4467779 := by
  apply nodeValid_prime [2, 7, 319127] ⟨4467779, 2, [(2, 1), (7, 1), (319127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_319127
  · decide +kernel

theorem prime_4543043 : Nat.Prime 4543043 := by
  apply nodeValid_prime [2, 7, 324503] ⟨4543043, 2, [(2, 1), (7, 1), (324503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_324503
  · decide +kernel

theorem prime_4629959 : Nat.Prime 4629959 := by
  apply nodeValid_prime [2, 19, 37, 89] ⟨4629959, 19, [(2, 1), (19, 1), (37, 2), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_89
  · decide +kernel

theorem prime_4975109 : Nat.Prime 4975109 := by
  apply nodeValid_prime [2, 613, 2029] ⟨4975109, 2, [(2, 2), (613, 1), (2029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_2029
  · decide +kernel

theorem prime_6189257 : Nat.Prime 6189257 := by
  apply nodeValid_prime [2, 773657] ⟨6189257, 3, [(2, 3), (773657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_773657
  · decide +kernel

theorem prime_6291293 : Nat.Prime 6291293 := by
  apply nodeValid_prime [2, 7, 17, 13217] ⟨6291293, 2, [(2, 2), (7, 1), (17, 1), (13217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_13217
  · decide +kernel

theorem prime_6433291 : Nat.Prime 6433291 := by
  apply nodeValid_prime [2, 3, 5, 23827] ⟨6433291, 7, [(2, 1), (3, 3), (5, 1), (23827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23827
  · decide +kernel

theorem prime_8203297 : Nat.Prime 8203297 := by
  apply nodeValid_prime [2, 3, 85451] ⟨8203297, 15, [(2, 5), (3, 1), (85451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_85451
  · decide +kernel

theorem prime_8673167 : Nat.Prime 8673167 := by
  apply nodeValid_prime [2, 4336583] ⟨8673167, 5, [(2, 1), (4336583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4336583
  · decide +kernel

theorem prime_8990543 : Nat.Prime 8990543 := by
  apply nodeValid_prime [2, 11, 97, 383] ⟨8990543, 5, [(2, 1), (11, 2), (97, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_97
    · exact prime_383
  · decide +kernel

theorem prime_9961151 : Nat.Prime 9961151 := by
  apply nodeValid_prime [2, 5, 17, 11719] ⟨9961151, 7, [(2, 1), (5, 2), (17, 1), (11719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_11719
  · decide +kernel

theorem prime_32758673 : Nat.Prime 32758673 := by
  apply nodeValid_prime [2, 41, 49937] ⟨32758673, 3, [(2, 4), (41, 1), (49937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_49937
  · decide +kernel

theorem prime_32813189 : Nat.Prime 32813189 := by
  apply nodeValid_prime [2, 8203297] ⟨32813189, 2, [(2, 2), (8203297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8203297
  · decide +kernel

theorem prime_34072949 : Nat.Prime 34072949 := by
  apply nodeValid_prime [2, 7, 13, 93607] ⟨34072949, 2, [(2, 2), (7, 1), (13, 1), (93607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_93607
  · decide +kernel

theorem prime_34184347 : Nat.Prime 34184347 := by
  apply nodeValid_prime [2, 3, 7, 179, 4547] ⟨34184347, 2, [(2, 1), (3, 1), (7, 1), (179, 1), (4547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_179
    · exact prime_4547
  · decide +kernel

theorem prime_35742233 : Nat.Prime 35742233 := by
  apply nodeValid_prime [2, 4467779] ⟨35742233, 3, [(2, 3), (4467779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4467779
  · decide +kernel

theorem prime_40952629 : Nat.Prime 40952629 := by
  apply nodeValid_prime [2, 3, 126397] ⟨40952629, 14, [(2, 2), (3, 4), (126397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_126397
  · decide +kernel

theorem prime_42105827 : Nat.Prime 42105827 := by
  apply nodeValid_prime [2, 7, 769, 3911] ⟨42105827, 2, [(2, 1), (7, 1), (769, 1), (3911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_769
    · exact prime_3911
  · decide +kernel

theorem prime_42117763 : Nat.Prime 42117763 := by
  apply nodeValid_prime [2, 3, 157, 44711] ⟨42117763, 2, [(2, 1), (3, 1), (157, 1), (44711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_44711
  · decide +kernel

theorem prime_45393151 : Nat.Prime 45393151 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 61] ⟨45393151, 15, [(2, 1), (3, 1), (5, 2), (11, 2), (41, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_61
  · decide +kernel

theorem prime_151236511 : Nat.Prime 151236511 := by
  apply nodeValid_prime [2, 3, 5, 991, 5087] ⟨151236511, 6, [(2, 1), (3, 1), (5, 1), (991, 1), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_991
    · exact prime_5087
  · decide +kernel

theorem prime_246037471 : Nat.Prime 246037471 := by
  apply nodeValid_prime [2, 3, 5, 7, 353, 3319] ⟨246037471, 11, [(2, 1), (3, 1), (5, 1), (7, 1), (353, 1), (3319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_353
    · exact prime_3319
  · decide +kernel

theorem prime_248507969 : Nat.Prime 248507969 := by
  apply nodeValid_prime [2, 3882937] ⟨248507969, 3, [(2, 6), (3882937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3882937
  · decide +kernel

theorem prime_360343733 : Nat.Prime 360343733 := by
  apply nodeValid_prime [2, 7, 197, 65327] ⟨360343733, 2, [(2, 2), (7, 1), (197, 1), (65327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_197
    · exact prime_65327
  · decide +kernel

theorem prime_479009537 : Nat.Prime 479009537 := by
  apply nodeValid_prime [2, 239, 7829] ⟨479009537, 3, [(2, 8), (239, 1), (7829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_7829
  · decide +kernel

theorem prime_544717813 : Nat.Prime 544717813 := by
  apply nodeValid_prime [2, 3, 45393151] ⟨544717813, 2, [(2, 2), (3, 1), (45393151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45393151
  · decide +kernel

theorem prime_578626327 : Nat.Prime 578626327 := by
  apply nodeValid_prime [2, 3, 157, 204751] ⟨578626327, 3, [(2, 1), (3, 2), (157, 1), (204751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_204751
  · decide +kernel

theorem prime_912924049 : Nat.Prime 912924049 := by
  apply nodeValid_prime [2, 3, 61, 311791] ⟨912924049, 13, [(2, 4), (3, 1), (61, 1), (311791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_311791
  · decide +kernel

theorem prime_1824765233 : Nat.Prime 1824765233 := by
  apply nodeValid_prime [2, 73, 997, 1567] ⟨1824765233, 3, [(2, 4), (73, 1), (997, 1), (1567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_997
    · exact prime_1567
  · decide +kernel

theorem prime_2044293187 : Nat.Prime 2044293187 := by
  apply nodeValid_prime [2, 3, 13, 43, 609509] ⟨2044293187, 3, [(2, 1), (3, 1), (13, 1), (43, 1), (609509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_609509
  · decide +kernel

theorem prime_2129536709 : Nat.Prime 2129536709 := by
  apply nodeValid_prime [2, 13, 40952629] ⟨2129536709, 2, [(2, 2), (13, 1), (40952629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_40952629
  · decide +kernel

theorem prime_3685396061 : Nat.Prime 3685396061 := by
  apply nodeValid_prime [2, 5, 59, 3123217] ⟨3685396061, 2, [(2, 2), (5, 1), (59, 1), (3123217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_3123217
  · decide +kernel

theorem prime_5378163311 : Nat.Prime 5378163311 := by
  apply nodeValid_prime [2, 5, 13, 73, 566719] ⟨5378163311, 22, [(2, 1), (5, 1), (13, 1), (73, 1), (566719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_73
    · exact prime_566719
  · decide +kernel

theorem prime_5641813693 : Nat.Prime 5641813693 := by
  apply nodeValid_prime [2, 3, 41, 3822367] ⟨5641813693, 2, [(2, 2), (3, 2), (41, 1), (3822367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_3822367
  · decide +kernel

theorem prime_9773668357 : Nat.Prime 9773668357 := by
  apply nodeValid_prime [2, 3, 17, 6151, 7789] ⟨9773668357, 5, [(2, 2), (3, 1), (17, 1), (6151, 1), (7789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_6151
    · exact prime_7789
  · decide +kernel

theorem prime_14288629969 : Nat.Prime 14288629969 := by
  apply nodeValid_prime [2, 3, 8387, 11831] ⟨14288629969, 14, [(2, 4), (3, 2), (8387, 1), (11831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8387
    · exact prime_11831
  · decide +kernel

theorem prime_20205512573 : Nat.Prime 20205512573 := by
  apply nodeValid_prime [2, 7, 263, 2743823] ⟨20205512573, 2, [(2, 2), (7, 1), (263, 1), (2743823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_263
    · exact prime_2743823
  · decide +kernel

theorem prime_22899580937 : Nat.Prime 22899580937 := by
  apply nodeValid_prime [2, 47441, 60337] ⟨22899580937, 3, [(2, 3), (47441, 1), (60337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47441
    · exact prime_60337
  · decide +kernel

theorem prime_25067929021 : Nat.Prime 25067929021 := by
  apply nodeValid_prime [2, 3, 5, 17, 409, 60089] ⟨25067929021, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (409, 1), (60089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_409
    · exact prime_60089
  · decide +kernel

theorem prime_39699340799 : Nat.Prime 39699340799 := by
  apply nodeValid_prime [2, 13, 53, 359, 6173] ⟨39699340799, 41, [(2, 1), (13, 2), (53, 1), (359, 1), (6173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_53
    · exact prime_359
    · exact prime_6173
  · decide +kernel

theorem prime_46262672779 : Nat.Prime 46262672779 := by
  apply nodeValid_prime [2, 3, 7, 127, 8673167] ⟨46262672779, 2, [(2, 1), (3, 1), (7, 1), (127, 1), (8673167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127
    · exact prime_8673167
  · decide +kernel

theorem prime_73849032473 : Nat.Prime 73849032473 := by
  apply nodeValid_prime [2, 5147, 1793497] ⟨73849032473, 3, [(2, 3), (5147, 1), (1793497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5147
    · exact prime_1793497
  · decide +kernel

theorem prime_93140009537 : Nat.Prime 93140009537 := by
  apply nodeValid_prime [2, 7, 23, 113, 167, 479] ⟨93140009537, 3, [(2, 6), (7, 1), (23, 1), (113, 1), (167, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_113
    · exact prime_167
    · exact prime_479
  · decide +kernel

theorem prime_137397485623 : Nat.Prime 137397485623 := by
  apply nodeValid_prime [2, 3, 22899580937] ⟨137397485623, 5, [(2, 1), (3, 1), (22899580937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22899580937
  · decide +kernel

theorem prime_171463559629 : Nat.Prime 171463559629 := by
  apply nodeValid_prime [2, 3, 14288629969] ⟨171463559629, 2, [(2, 2), (3, 1), (14288629969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14288629969
  · decide +kernel

theorem prime_343777253959 : Nat.Prime 343777253959 := by
  apply nodeValid_prime [2, 3, 19, 37, 83, 327319] ⟨343777253959, 3, [(2, 1), (3, 2), (19, 1), (37, 1), (83, 1), (327319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_83
    · exact prime_327319
  · decide +kernel

theorem prime_411172856401 : Nat.Prime 411172856401 := by
  apply nodeValid_prime [2, 3, 5, 2089, 164023] ⟨411172856401, 7, [(2, 4), (3, 1), (5, 2), (2089, 1), (164023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2089
    · exact prime_164023
  · decide +kernel

theorem prime_516091431059 : Nat.Prime 516091431059 := by
  apply nodeValid_prime [2, 7, 17, 853, 2542147] ⟨516091431059, 2, [(2, 1), (7, 1), (17, 1), (853, 1), (2542147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_853
    · exact prime_2542147
  · decide +kernel

theorem prime_680207157187 : Nat.Prime 680207157187 := by
  apply nodeValid_prime [2, 3, 19, 599, 9961151] ⟨680207157187, 5, [(2, 1), (3, 1), (19, 1), (599, 1), (9961151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_599
    · exact prime_9961151
  · decide +kernel

theorem prime_683591604341 : Nat.Prime 683591604341 := by
  apply nodeValid_prime [2, 5, 47, 701, 1037411] ⟨683591604341, 3, [(2, 2), (5, 1), (47, 1), (701, 1), (1037411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_701
    · exact prime_1037411
  · decide +kernel

theorem prime_4061004411521 : Nat.Prime 4061004411521 := by
  apply nodeValid_prime [2, 5, 7, 29, 5147, 6073] ⟨4061004411521, 3, [(2, 7), (5, 1), (7, 1), (29, 1), (5147, 1), (6073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_5147
    · exact prime_6073
  · decide +kernel

theorem prime_4061004412847 : Nat.Prime 4061004412847 := by
  apply nodeValid_prime [2, 1249, 8737, 186071] ⟨4061004412847, 5, [(2, 1), (1249, 1), (8737, 1), (186071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1249
    · exact prime_8737
    · exact prime_186071
  · decide +kernel

theorem prime_4061004501403 : Nat.Prime 4061004501403 := by
  apply nodeValid_prime [2, 3, 25067929021] ⟨4061004501403, 3, [(2, 1), (3, 4), (25067929021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25067929021
  · decide +kernel

theorem prime_4064372755097 : Nat.Prime 4064372755097 := by
  apply nodeValid_prime [2, 56509, 8990543] ⟨4064372755097, 3, [(2, 3), (56509, 1), (8990543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_56509
    · exact prime_8990543
  · decide +kernel

theorem prime_4064372755787 : Nat.Prime 4064372755787 := by
  apply nodeValid_prime [2, 7, 358073, 810763] ⟨4064372755787, 5, [(2, 1), (7, 1), (358073, 1), (810763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_358073
    · exact prime_810763
  · decide +kernel

theorem prime_4064372842297 : Nat.Prime 4064372842297 := by
  apply nodeValid_prime [2, 3, 13, 397, 32813189] ⟨4064372842297, 14, [(2, 3), (3, 1), (13, 1), (397, 1), (32813189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_397
    · exact prime_32813189
  · decide +kernel

theorem prime_4067743078631 : Nat.Prime 4067743078631 := by
  apply nodeValid_prime [2, 5, 7, 11, 163, 4629959] ⟨4067743078631, 13, [(2, 1), (5, 1), (7, 2), (11, 1), (163, 1), (4629959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_163
    · exact prime_4629959
  · decide +kernel

theorem prime_4067743078811 : Nat.Prime 4067743078811 := by
  apply nodeValid_prime [2, 5, 19, 37, 578626327] ⟨4067743078811, 2, [(2, 1), (5, 1), (19, 1), (37, 1), (578626327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_37
    · exact prime_578626327
  · decide +kernel

theorem prime_4067743080001 : Nat.Prime 4067743080001 := by
  apply nodeValid_prime [2, 3, 5, 199, 170341] ⟨4067743080001, 14, [(2, 6), (3, 1), (5, 4), (199, 1), (170341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_170341
  · decide +kernel

theorem prime_4071115204553 : Nat.Prime 4071115204553 := by
  apply nodeValid_prime [2, 11, 46262672779] ⟨4071115204553, 3, [(2, 3), (11, 1), (46262672779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_46262672779
  · decide +kernel

theorem prime_4071115210621 : Nat.Prime 4071115210621 := by
  apply nodeValid_prime [2, 3, 5, 53, 199, 6433291] ⟨4071115210621, 6, [(2, 2), (3, 1), (5, 1), (53, 1), (199, 1), (6433291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_199
    · exact prime_6433291
  · decide +kernel

theorem prime_4071115211323 : Nat.Prime 4071115211323 := by
  apply nodeValid_prime [2, 3, 127, 51257, 104233] ⟨4071115211323, 3, [(2, 1), (3, 1), (127, 1), (51257, 1), (104233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_51257
    · exact prime_104233
  · decide +kernel

theorem prime_4074489222233 : Nat.Prime 4074489222233 := by
  apply nodeValid_prime [2, 11, 13, 6451, 552103] ⟨4074489222233, 3, [(2, 3), (11, 1), (13, 1), (6451, 1), (552103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_6451
    · exact prime_552103
  · decide +kernel

theorem prime_4074489240119 : Nat.Prime 4074489240119 := by
  apply nodeValid_prime [2, 11, 17, 31, 37, 857, 11083] ⟨4074489240119, 7, [(2, 1), (11, 1), (17, 1), (31, 1), (37, 1), (857, 1), (11083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_31
    · exact prime_37
    · exact prime_857
    · exact prime_11083
  · decide +kernel

theorem prime_4074489241241 : Nat.Prime 4074489241241 := by
  apply nodeValid_prime [2, 5, 11, 17, 544717813] ⟨4074489241241, 3, [(2, 3), (5, 1), (11, 1), (17, 1), (544717813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_544717813
  · decide +kernel

theorem prime_4077865131569 : Nat.Prime 4077865131569 := by
  apply nodeValid_prime [2, 17, 2383, 6291293] ⟨4077865131569, 3, [(2, 4), (17, 1), (2383, 1), (6291293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2383
    · exact prime_6291293
  · decide +kernel

theorem prime_4077865132387 : Nat.Prime 4077865132387 := by
  apply nodeValid_prime [2, 3, 20747, 32758673] ⟨4077865132387, 2, [(2, 1), (3, 1), (20747, 1), (32758673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20747
    · exact prime_32758673
  · decide +kernel

theorem prime_4077865133297 : Nat.Prime 4077865133297 := by
  apply nodeValid_prime [2, 6053, 42105827] ⟨4077865133297, 3, [(2, 4), (6053, 1), (42105827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6053
    · exact prime_42105827
  · decide +kernel

theorem prime_4081242902981 : Nat.Prime 4081242902981 := by
  apply nodeValid_prime [2, 5, 17, 52369, 229213] ⟨4081242902981, 2, [(2, 2), (5, 1), (17, 1), (52369, 1), (229213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_52369
    · exact prime_229213
  · decide +kernel

theorem prime_4081242903827 : Nat.Prime 4081242903827 := by
  apply nodeValid_prime [2, 11, 79999, 2318917] ⟨4081242903827, 2, [(2, 1), (11, 1), (79999, 1), (2318917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79999
    · exact prime_2318917
  · decide +kernel

theorem prime_4081242943123 : Nat.Prime 4081242943123 := by
  apply nodeValid_prime [2, 3, 680207157187] ⟨4081242943123, 2, [(2, 1), (3, 1), (680207157187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_680207157187
  · decide +kernel

theorem prime_4084622646199 : Nat.Prime 4084622646199 := by
  apply nodeValid_prime [2, 3, 37, 75289, 244381] ⟨4084622646199, 3, [(2, 1), (3, 1), (37, 1), (75289, 1), (244381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_75289
    · exact prime_244381
  · decide +kernel

theorem prime_4084622703043 : Nat.Prime 4084622703043 := by
  apply nodeValid_prime [2, 3, 7, 21407, 4543043] ⟨4084622703043, 11, [(2, 1), (3, 1), (7, 1), (21407, 1), (4543043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_21407
    · exact prime_4543043
  · decide +kernel

theorem prime_4084622703943 : Nat.Prime 4084622703943 := by
  apply nodeValid_prime [2, 3, 11, 467, 1693, 78277] ⟨4084622703943, 3, [(2, 1), (3, 1), (11, 1), (467, 1), (1693, 1), (78277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_467
    · exact prime_1693
    · exact prime_78277
  · decide +kernel

theorem prime_4088004248501 : Nat.Prime 4088004248501 := by
  apply nodeValid_prime [2, 5, 1321, 6189257] ⟨4088004248501, 2, [(2, 2), (5, 3), (1321, 1), (6189257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1321
    · exact prime_6189257
  · decide +kernel

theorem prime_4088004275123 : Nat.Prime 4088004275123 := by
  apply nodeValid_prime [2, 239, 251, 34072949] ⟨4088004275123, 2, [(2, 1), (239, 1), (251, 1), (34072949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_251
    · exact prime_34072949
  · decide +kernel

theorem prime_4088004276353 : Nat.Prime 4088004276353 := by
  apply nodeValid_prime [2, 19, 1031, 1630381] ⟨4088004276353, 3, [(2, 7), (19, 1), (1031, 1), (1630381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1031
    · exact prime_1630381
  · decide +kernel

theorem prime_4091387755043 : Nat.Prime 4091387755043 := by
  apply nodeValid_prime [2, 7, 83, 103, 34184347] ⟨4091387755043, 5, [(2, 1), (7, 1), (83, 1), (103, 1), (34184347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
    · exact prime_103
    · exact prime_34184347
  · decide +kernel

theorem prime_4091387757679 : Nat.Prime 4091387757679 := by
  apply nodeValid_prime [2, 3, 13, 22811, 255499] ⟨4091387757679, 19, [(2, 1), (3, 3), (13, 1), (22811, 1), (255499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_22811
    · exact prime_255499
  · decide +kernel

theorem prime_4091387760697 : Nat.Prime 4091387760697 := by
  apply nodeValid_prime [2, 3, 313, 18313, 29741] ⟨4091387760697, 5, [(2, 3), (3, 1), (313, 1), (18313, 1), (29741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
    · exact prime_18313
    · exact prime_29741
  · decide +kernel

theorem prime_4094773154387 : Nat.Prime 4094773154387 := by
  apply nodeValid_prime [2, 48611, 42117763] ⟨4094773154387, 2, [(2, 1), (48611, 1), (42117763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_48611
    · exact prime_42117763
  · decide +kernel

theorem prime_4094773181413 : Nat.Prime 4094773181413 := by
  apply nodeValid_prime [2, 3, 9547, 35742233] ⟨4094773181413, 2, [(2, 2), (3, 1), (9547, 1), (35742233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9547
    · exact prime_35742233
  · decide +kernel

theorem prime_4094773182853 : Nat.Prime 4094773182853 := by
  apply nodeValid_prime [2, 3, 11, 17, 1824765233] ⟨4094773182853, 2, [(2, 2), (3, 1), (11, 1), (17, 1), (1824765233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_1824765233
  · decide +kernel

theorem prime_4098160419629 : Nat.Prime 4098160419629 := by
  apply nodeValid_prime [2, 11, 93140009537] ⟨4098160419629, 2, [(2, 2), (11, 1), (93140009537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_93140009537
  · decide +kernel

theorem prime_4098160419833 : Nat.Prime 4098160419833 := by
  apply nodeValid_prime [2, 139, 3685396061] ⟨4098160419833, 3, [(2, 3), (139, 1), (3685396061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_3685396061
  · decide +kernel

theorem prime_4098160442983 : Nat.Prime 4098160442983 := by
  apply nodeValid_prime [2, 3, 127, 5378163311] ⟨4098160442983, 3, [(2, 1), (3, 1), (127, 1), (5378163311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_5378163311
  · decide +kernel

theorem prime_4101549626017 : Nat.Prime 4101549626017 := by
  apply nodeValid_prime [2, 3, 521, 3037213] ⟨4101549626017, 5, [(2, 5), (3, 4), (521, 1), (3037213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_3037213
  · decide +kernel

theorem prime_4101549626047 : Nat.Prime 4101549626047 := by
  apply nodeValid_prime [2, 3, 683591604341] ⟨4101549626047, 5, [(2, 1), (3, 1), (683591604341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683591604341
  · decide +kernel

theorem prime_4101549628243 : Nat.Prime 4101549628243 := by
  apply nodeValid_prime [2, 3, 11, 97, 173, 3703277] ⟨4101549628243, 3, [(2, 1), (3, 1), (11, 1), (97, 1), (173, 1), (3703277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_173
    · exact prime_3703277
  · decide +kernel

theorem prime_4104940709941 : Nat.Prime 4104940709941 := by
  apply nodeValid_prime [2, 3, 5, 7, 9773668357] ⟨4104940709941, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (9773668357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_9773668357
  · decide +kernel

theorem prime_4104940718261 : Nat.Prime 4104940718261 := by
  apply nodeValid_prime [2, 5, 29, 52879, 133843] ⟨4104940718261, 2, [(2, 2), (5, 1), (29, 1), (52879, 1), (133843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_52879
    · exact prime_133843
  · decide +kernel

theorem prime_4104940719497 : Nat.Prime 4104940719497 := by
  apply nodeValid_prime [2, 251, 2044293187] ⟨4104940719497, 3, [(2, 3), (251, 1), (2044293187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_2044293187
  · decide +kernel

theorem prime_4108333690759 : Nat.Prime 4108333690759 := by
  apply nodeValid_prime [2, 3, 11, 23, 246037471] ⟨4108333690759, 7, [(2, 1), (3, 1), (11, 2), (23, 1), (246037471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_246037471
  · decide +kernel

theorem prime_4108333743509 : Nat.Prime 4108333743509 := by
  apply nodeValid_prime [2, 4133, 248507969] ⟨4108333743509, 2, [(2, 2), (4133, 1), (248507969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4133
    · exact prime_248507969
  · decide +kernel

theorem prime_4108333743907 : Nat.Prime 4108333743907 := by
  apply nodeValid_prime [2, 3, 7, 17, 17033, 48259] ⟨4108333743907, 5, [(2, 1), (3, 1), (7, 2), (17, 1), (17033, 1), (48259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_17033
    · exact prime_48259
  · decide +kernel

theorem prime_4111728564011 : Nat.Prime 4111728564011 := by
  apply nodeValid_prime [2, 5, 411172856401] ⟨4111728564011, 2, [(2, 1), (5, 1), (411172856401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_411172856401
  · decide +kernel

theorem prime_4111728583751 : Nat.Prime 4111728583751 := by
  apply nodeValid_prime [2, 5, 3797, 866311] ⟨4111728583751, 19, [(2, 1), (5, 4), (3797, 1), (866311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3797
    · exact prime_866311
  · decide +kernel

theorem prime_4111728584141 : Nat.Prime 4111728584141 := by
  apply nodeValid_prime [2, 5, 31, 43, 4975109] ⟨4111728584141, 3, [(2, 2), (5, 1), (31, 2), (43, 1), (4975109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_43
    · exact prime_4975109
  · decide +kernel

theorem prime_4115125329323 : Nat.Prime 4115125329323 := by
  apply nodeValid_prime [2, 7, 43, 439, 2224457] ⟨4115125329323, 5, [(2, 1), (7, 2), (43, 1), (439, 1), (2224457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_439
    · exact prime_2224457
  · decide +kernel

theorem prime_4115125430861 : Nat.Prime 4115125430861 := by
  apply nodeValid_prime [2, 5, 571, 360343733] ⟨4115125430861, 2, [(2, 2), (5, 1), (571, 1), (360343733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_571
    · exact prime_360343733
  · decide +kernel

theorem prime_4115125431097 : Nat.Prime 4115125431097 := by
  apply nodeValid_prime [2, 3, 171463559629] ⟨4115125431097, 10, [(2, 3), (3, 1), (171463559629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_171463559629
  · decide +kernel

theorem prime_4118523995207 : Nat.Prime 4118523995207 := by
  apply nodeValid_prime [2, 967, 2129536709] ⟨4118523995207, 5, [(2, 1), (967, 1), (2129536709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_967
    · exact prime_2129536709
  · decide +kernel

theorem prime_4118523995891 : Nat.Prime 4118523995891 := by
  apply nodeValid_prime [2, 5, 73, 5641813693] ⟨4118523995891, 6, [(2, 1), (5, 1), (73, 1), (5641813693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_5641813693
  · decide +kernel

theorem prime_4118523999127 : Nat.Prime 4118523999127 := by
  apply nodeValid_prime [2, 3, 1433, 479009537] ⟨4118523999127, 3, [(2, 1), (3, 1), (1433, 1), (479009537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1433
    · exact prime_479009537
  · decide +kernel

theorem prime_4121924558989 : Nat.Prime 4121924558989 := by
  apply nodeValid_prime [2, 3, 92381, 3718229] ⟨4121924558989, 10, [(2, 2), (3, 1), (92381, 1), (3718229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_92381
    · exact prime_3718229
  · decide +kernel

theorem prime_4121924564893 : Nat.Prime 4121924564893 := by
  apply nodeValid_prime [2, 3, 17, 20205512573] ⟨4121924564893, 2, [(2, 2), (3, 1), (17, 1), (20205512573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_20205512573
  · decide +kernel

theorem prime_4121924568691 : Nat.Prime 4121924568691 := by
  apply nodeValid_prime [2, 3, 5, 137397485623] ⟨4121924568691, 2, [(2, 1), (3, 1), (5, 1), (137397485623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137397485623
  · decide +kernel

theorem prime_4125327047509 : Nat.Prime 4125327047509 := by
  apply nodeValid_prime [2, 3, 343777253959] ⟨4125327047509, 2, [(2, 2), (3, 1), (343777253959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_343777253959
  · decide +kernel

theorem prime_4125327107107 : Nat.Prime 4125327107107 := by
  apply nodeValid_prime [2, 3, 17, 35731, 1131913] ⟨4125327107107, 2, [(2, 1), (3, 1), (17, 1), (35731, 1), (1131913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_35731
    · exact prime_1131913
  · decide +kernel

theorem prime_4125327108997 : Nat.Prime 4125327108997 := by
  apply nodeValid_prime [2, 3, 137, 751, 3341309] ⟨4125327108997, 2, [(2, 2), (3, 1), (137, 1), (751, 1), (3341309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_751
    · exact prime_3341309
  · decide +kernel

theorem prime_4128731443097 : Nat.Prime 4128731443097 := by
  apply nodeValid_prime [2, 13, 39699340799] ⟨4128731443097, 3, [(2, 3), (13, 1), (39699340799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_39699340799
  · decide +kernel

theorem prime_4128731448473 : Nat.Prime 4128731448473 := by
  apply nodeValid_prime [2, 516091431059] ⟨4128731448473, 3, [(2, 3), (516091431059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_516091431059
  · decide +kernel

theorem prime_4128731448551 : Nat.Prime 4128731448551 := by
  apply nodeValid_prime [2, 5, 29, 16493, 172643] ⟨4128731448551, 13, [(2, 1), (5, 2), (29, 1), (16493, 1), (172643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_16493
    · exact prime_172643
  · decide +kernel

theorem prime_4132137746003 : Nat.Prime 4132137746003 := by
  apply nodeValid_prime [2, 7, 426871, 691433] ⟨4132137746003, 2, [(2, 1), (7, 1), (426871, 1), (691433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_426871
    · exact prime_691433
  · decide +kernel

theorem prime_4132137832787 : Nat.Prime 4132137832787 := by
  apply nodeValid_prime [2, 59, 87359, 400853] ⟨4132137832787, 2, [(2, 1), (59, 1), (87359, 1), (400853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_87359
    · exact prime_400853
  · decide +kernel

theorem prime_4132137833849 : Nat.Prime 4132137833849 := by
  apply nodeValid_prime [2, 29, 59, 11393, 26497] ⟨4132137833849, 3, [(2, 3), (29, 1), (59, 1), (11393, 1), (26497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_59
    · exact prime_11393
    · exact prime_26497
  · decide +kernel

theorem prime_4135545818489 : Nat.Prime 4135545818489 := by
  apply nodeValid_prime [2, 7, 73849032473] ⟨4135545818489, 3, [(2, 3), (7, 1), (73849032473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73849032473
  · decide +kernel

theorem prime_4135545818497 : Nat.Prime 4135545818497 := by
  apply nodeValid_prime [2, 3, 17, 29, 37, 197] ⟨4135545818497, 5, [(2, 7), (3, 5), (17, 1), (29, 1), (37, 2), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_37
    · exact prime_197
  · decide +kernel

theorem prime_4135545941971 : Nat.Prime 4135545941971 := by
  apply nodeValid_prime [2, 3, 5, 151, 912924049] ⟨4135545941971, 3, [(2, 1), (3, 1), (5, 1), (151, 1), (912924049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_912924049
  · decide +kernel

theorem prime_4138956033139 : Nat.Prime 4138956033139 := by
  apply nodeValid_prime [2, 3, 77557, 988271] ⟨4138956033139, 3, [(2, 1), (3, 3), (77557, 1), (988271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_77557
    · exact prime_988271
  · decide +kernel

theorem prime_4138956110209 : Nat.Prime 4138956110209 := by
  apply nodeValid_prime [2, 3, 100313, 107449] ⟨4138956110209, 11, [(2, 7), (3, 1), (100313, 1), (107449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_100313
    · exact prime_107449
  · decide +kernel

theorem prime_4138956112783 : Nat.Prime 4138956112783 := by
  apply nodeValid_prime [2, 3, 263, 21943, 119533] ⟨4138956112783, 3, [(2, 1), (3, 1), (263, 1), (21943, 1), (119533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_21943
    · exact prime_119533
  · decide +kernel

theorem prime_4142368036291 : Nat.Prime 4142368036291 := by
  apply nodeValid_prime [2, 3, 5, 11, 83, 151236511] ⟨4142368036291, 10, [(2, 1), (3, 1), (5, 1), (11, 1), (83, 1), (151236511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_83
    · exact prime_151236511
  · decide +kernel

theorem prime_4142368078747 : Nat.Prime 4142368078747 := by
  apply nodeValid_prime [2, 3, 73, 15137, 624791] ⟨4142368078747, 2, [(2, 1), (3, 1), (73, 1), (15137, 1), (624791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_15137
    · exact prime_624791
  · decide +kernel

theorem prime_4142368078991 : Nat.Prime 4142368078991 := by
  apply nodeValid_prime [2, 5, 347, 349, 3420533] ⟨4142368078991, 7, [(2, 1), (5, 1), (347, 1), (349, 1), (3420533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_347
    · exact prime_349
    · exact prime_3420533
  · decide +kernel

end Sude.Lucas.Generated
