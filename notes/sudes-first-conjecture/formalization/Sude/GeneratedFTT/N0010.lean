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

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_769 : Nat.Prime 769 := by
  apply nodeValid_prime [2, 3] ⟨769, 11, [(2, 8), (3, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_983 : Nat.Prime 983 := by
  apply nodeValid_prime [2, 491] ⟨983, 5, [(2, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_491
  · decide +kernel

theorem prime_1021 : Nat.Prime 1021 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨1021, 10, [(2, 2), (3, 1), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_1063 : Nat.Prime 1063 := by
  apply nodeValid_prime [2, 3, 59] ⟨1063, 3, [(2, 1), (3, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_1429 : Nat.Prime 1429 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨1429, 6, [(2, 2), (3, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_1877 : Nat.Prime 1877 := by
  apply nodeValid_prime [2, 7, 67] ⟨1877, 2, [(2, 2), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_1889 : Nat.Prime 1889 := by
  apply nodeValid_prime [2, 59] ⟨1889, 3, [(2, 5), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59
  · decide +kernel

theorem prime_2161 : Nat.Prime 2161 := by
  apply nodeValid_prime [2, 3, 5] ⟨2161, 23, [(2, 4), (3, 3), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_2243 : Nat.Prime 2243 := by
  apply nodeValid_prime [2, 19, 59] ⟨2243, 2, [(2, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_2287 : Nat.Prime 2287 := by
  apply nodeValid_prime [2, 3, 127] ⟨2287, 19, [(2, 1), (3, 2), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
  · decide +kernel

theorem prime_2399 : Nat.Prime 2399 := by
  apply nodeValid_prime [2, 11, 109] ⟨2399, 11, [(2, 1), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_2459 : Nat.Prime 2459 := by
  apply nodeValid_prime [2, 1229] ⟨2459, 2, [(2, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1229
  · decide +kernel

theorem prime_2531 : Nat.Prime 2531 := by
  apply nodeValid_prime [2, 5, 11, 23] ⟨2531, 2, [(2, 1), (5, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_2549 : Nat.Prime 2549 := by
  apply nodeValid_prime [2, 7, 13] ⟨2549, 2, [(2, 2), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_2711 : Nat.Prime 2711 := by
  apply nodeValid_prime [2, 5, 271] ⟨2711, 7, [(2, 1), (5, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
  · decide +kernel

theorem prime_3229 : Nat.Prime 3229 := by
  apply nodeValid_prime [2, 3, 269] ⟨3229, 6, [(2, 2), (3, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
  · decide +kernel

theorem prime_3329 : Nat.Prime 3329 := by
  apply nodeValid_prime [2, 13] ⟨3329, 3, [(2, 8), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13
  · decide +kernel

theorem prime_3779 : Nat.Prime 3779 := by
  apply nodeValid_prime [2, 1889] ⟨3779, 2, [(2, 1), (1889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1889
  · decide +kernel

theorem prime_4091 : Nat.Prime 4091 := by
  apply nodeValid_prime [2, 5, 409] ⟨4091, 2, [(2, 1), (5, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
  · decide +kernel

theorem prime_4561 : Nat.Prime 4561 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨4561, 11, [(2, 4), (3, 1), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_4759 : Nat.Prime 4759 := by
  apply nodeValid_prime [2, 3, 13, 61] ⟨4759, 3, [(2, 1), (3, 1), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_4919 : Nat.Prime 4919 := by
  apply nodeValid_prime [2, 2459] ⟨4919, 13, [(2, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2459
  · decide +kernel

theorem prime_5417 : Nat.Prime 5417 := by
  apply nodeValid_prime [2, 677] ⟨5417, 3, [(2, 3), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_677
  · decide +kernel

theorem prime_5693 : Nat.Prime 5693 := by
  apply nodeValid_prime [2, 1423] ⟨5693, 2, [(2, 2), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1423
  · decide +kernel

theorem prime_5903 : Nat.Prime 5903 := by
  apply nodeValid_prime [2, 13, 227] ⟨5903, 5, [(2, 1), (13, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_227
  · decide +kernel

theorem prime_6089 : Nat.Prime 6089 := by
  apply nodeValid_prime [2, 761] ⟨6089, 3, [(2, 3), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_761
  · decide +kernel

theorem prime_6151 : Nat.Prime 6151 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨6151, 3, [(2, 1), (3, 1), (5, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_7559 : Nat.Prime 7559 := by
  apply nodeValid_prime [2, 3779] ⟨7559, 13, [(2, 1), (3779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3779
  · decide +kernel

theorem prime_7649 : Nat.Prime 7649 := by
  apply nodeValid_prime [2, 239] ⟨7649, 3, [(2, 5), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_239
  · decide +kernel

theorem prime_8221 : Nat.Prime 8221 := by
  apply nodeValid_prime [2, 3, 5, 137] ⟨8221, 2, [(2, 2), (3, 1), (5, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_8539 : Nat.Prime 8539 := by
  apply nodeValid_prime [2, 3, 1423] ⟨8539, 2, [(2, 1), (3, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1423
  · decide +kernel

theorem prime_9173 : Nat.Prime 9173 := by
  apply nodeValid_prime [2, 2293] ⟨9173, 2, [(2, 2), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2293
  · decide +kernel

theorem prime_9377 : Nat.Prime 9377 := by
  apply nodeValid_prime [2, 293] ⟨9377, 3, [(2, 5), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_293
  · decide +kernel

theorem prime_9929 : Nat.Prime 9929 := by
  apply nodeValid_prime [2, 17, 73] ⟨9929, 3, [(2, 3), (17, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_73
  · decide +kernel

theorem prime_11047 : Nat.Prime 11047 := by
  apply nodeValid_prime [2, 3, 7, 263] ⟨11047, 3, [(2, 1), (3, 1), (7, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_263
  · decide +kernel

theorem prime_11383 : Nat.Prime 11383 := by
  apply nodeValid_prime [2, 3, 7, 271] ⟨11383, 5, [(2, 1), (3, 1), (7, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_271
  · decide +kernel

theorem prime_11953 : Nat.Prime 11953 := by
  apply nodeValid_prime [2, 3, 83] ⟨11953, 5, [(2, 4), (3, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_13763 : Nat.Prime 13763 := by
  apply nodeValid_prime [2, 7, 983] ⟨13763, 2, [(2, 1), (7, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_983
  · decide +kernel

theorem prime_13907 : Nat.Prime 13907 := by
  apply nodeValid_prime [2, 17, 409] ⟨13907, 2, [(2, 1), (17, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_409
  · decide +kernel

theorem prime_14221 : Nat.Prime 14221 := by
  apply nodeValid_prime [2, 3, 5, 79] ⟨14221, 2, [(2, 2), (3, 2), (5, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_15137 : Nat.Prime 15137 := by
  apply nodeValid_prime [2, 11, 43] ⟨15137, 3, [(2, 5), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_15373 : Nat.Prime 15373 := by
  apply nodeValid_prime [2, 3, 7, 61] ⟨15373, 2, [(2, 2), (3, 2), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_15787 : Nat.Prime 15787 := by
  apply nodeValid_prime [2, 3, 877] ⟨15787, 2, [(2, 1), (3, 2), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_877
  · decide +kernel

theorem prime_17041 : Nat.Prime 17041 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨17041, 7, [(2, 4), (3, 1), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_17573 : Nat.Prime 17573 := by
  apply nodeValid_prime [2, 23, 191] ⟨17573, 2, [(2, 2), (23, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_191
  · decide +kernel

theorem prime_19913 : Nat.Prime 19913 := by
  apply nodeValid_prime [2, 19, 131] ⟨19913, 3, [(2, 3), (19, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_131
  · decide +kernel

theorem prime_20021 : Nat.Prime 20021 := by
  apply nodeValid_prime [2, 5, 7, 11, 13] ⟨20021, 3, [(2, 2), (5, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_20393 : Nat.Prime 20393 := by
  apply nodeValid_prime [2, 2549] ⟨20393, 3, [(2, 3), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2549
  · decide +kernel

theorem prime_20533 : Nat.Prime 20533 := by
  apply nodeValid_prime [2, 3, 29, 59] ⟨20533, 2, [(2, 2), (3, 1), (29, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_59
  · decide +kernel

theorem prime_21169 : Nat.Prime 21169 := by
  apply nodeValid_prime [2, 3, 7] ⟨21169, 13, [(2, 4), (3, 3), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_23857 : Nat.Prime 23857 := by
  apply nodeValid_prime [2, 3, 7, 71] ⟨23857, 5, [(2, 4), (3, 1), (7, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_24547 : Nat.Prime 24547 := by
  apply nodeValid_prime [2, 3, 4091] ⟨24547, 2, [(2, 1), (3, 1), (4091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4091
  · decide +kernel

theorem prime_27527 : Nat.Prime 27527 := by
  apply nodeValid_prime [2, 13763] ⟨27527, 5, [(2, 1), (13763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13763
  · decide +kernel

theorem prime_29147 : Nat.Prime 29147 := by
  apply nodeValid_prime [2, 13, 19, 59] ⟨29147, 2, [(2, 1), (13, 1), (19, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_29287 : Nat.Prime 29287 := by
  apply nodeValid_prime [2, 3, 1627] ⟨29287, 5, [(2, 1), (3, 2), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1627
  · decide +kernel

theorem prime_29761 : Nat.Prime 29761 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨29761, 17, [(2, 6), (3, 1), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_30223 : Nat.Prime 30223 := by
  apply nodeValid_prime [2, 3, 23, 73] ⟨30223, 3, [(2, 1), (3, 2), (23, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_73
  · decide +kernel

theorem prime_31727 : Nat.Prime 31727 := by
  apply nodeValid_prime [2, 29, 547] ⟨31727, 5, [(2, 1), (29, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_547
  · decide +kernel

theorem prime_32533 : Nat.Prime 32533 := by
  apply nodeValid_prime [2, 3, 2711] ⟨32533, 2, [(2, 2), (3, 1), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2711
  · decide +kernel

theorem prime_34157 : Nat.Prime 34157 := by
  apply nodeValid_prime [2, 8539] ⟨34157, 2, [(2, 2), (8539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8539
  · decide +kernel

theorem prime_38317 : Nat.Prime 38317 := by
  apply nodeValid_prime [2, 3, 31, 103] ⟨38317, 2, [(2, 2), (3, 1), (31, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_103
  · decide +kernel

theorem prime_39827 : Nat.Prime 39827 := by
  apply nodeValid_prime [2, 19913] ⟨39827, 2, [(2, 1), (19913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19913
  · decide +kernel

theorem prime_40787 : Nat.Prime 40787 := by
  apply nodeValid_prime [2, 20393] ⟨40787, 2, [(2, 1), (20393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20393
  · decide +kernel

theorem prime_44531 : Nat.Prime 44531 := by
  apply nodeValid_prime [2, 5, 61, 73] ⟨44531, 2, [(2, 1), (5, 1), (61, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_73
  · decide +kernel

theorem prime_47981 : Nat.Prime 47981 := by
  apply nodeValid_prime [2, 5, 2399] ⟨47981, 2, [(2, 2), (5, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2399
  · decide +kernel

theorem prime_49409 : Nat.Prime 49409 := by
  apply nodeValid_prime [2, 193] ⟨49409, 3, [(2, 8), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_193
  · decide +kernel

theorem prime_52631 : Nat.Prime 52631 := by
  apply nodeValid_prime [2, 5, 19, 277] ⟨52631, 13, [(2, 1), (5, 1), (19, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_277
  · decide +kernel

theorem prime_54037 : Nat.Prime 54037 := by
  apply nodeValid_prime [2, 3, 19, 79] ⟨54037, 2, [(2, 2), (3, 2), (19, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_79
  · decide +kernel

theorem prime_63149 : Nat.Prime 63149 := by
  apply nodeValid_prime [2, 15787] ⟨63149, 2, [(2, 2), (15787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15787
  · decide +kernel

theorem prime_76081 : Nat.Prime 76081 := by
  apply nodeValid_prime [2, 3, 5, 317] ⟨76081, 7, [(2, 4), (3, 1), (5, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_317
  · decide +kernel

theorem prime_77167 : Nat.Prime 77167 := by
  apply nodeValid_prime [2, 3, 1429] ⟨77167, 21, [(2, 1), (3, 3), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1429
  · decide +kernel

theorem prime_84391 : Nat.Prime 84391 := by
  apply nodeValid_prime [2, 3, 5, 29, 97] ⟨84391, 3, [(2, 1), (3, 1), (5, 1), (29, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_97
  · decide +kernel

theorem prime_90709 : Nat.Prime 90709 := by
  apply nodeValid_prime [2, 3, 7559] ⟨90709, 6, [(2, 2), (3, 1), (7559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7559
  · decide +kernel

theorem prime_90823 : Nat.Prime 90823 := by
  apply nodeValid_prime [2, 3, 15137] ⟨90823, 6, [(2, 1), (3, 1), (15137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15137
  · decide +kernel

theorem prime_94207 : Nat.Prime 94207 := by
  apply nodeValid_prime [2, 3, 7, 2243] ⟨94207, 6, [(2, 1), (3, 1), (7, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2243
  · decide +kernel

theorem prime_95429 : Nat.Prime 95429 := by
  apply nodeValid_prime [2, 23857] ⟨95429, 2, [(2, 2), (23857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23857
  · decide +kernel

theorem prime_110039 : Nat.Prime 110039 := by
  apply nodeValid_prime [2, 37, 1487] ⟨110039, 13, [(2, 1), (37, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1487
  · decide +kernel

theorem prime_124721 : Nat.Prime 124721 := by
  apply nodeValid_prime [2, 5, 1559] ⟨124721, 3, [(2, 4), (5, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1559
  · decide +kernel

theorem prime_154841 : Nat.Prime 154841 := by
  apply nodeValid_prime [2, 5, 7, 79] ⟨154841, 15, [(2, 3), (5, 1), (7, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_175723 : Nat.Prime 175723 := by
  apply nodeValid_prime [2, 3, 29287] ⟨175723, 2, [(2, 1), (3, 1), (29287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29287
  · decide +kernel

theorem prime_213461 : Nat.Prime 213461 := by
  apply nodeValid_prime [2, 5, 13, 821] ⟨213461, 3, [(2, 2), (5, 1), (13, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_821
  · decide +kernel

theorem prime_245471 : Nat.Prime 245471 := by
  apply nodeValid_prime [2, 5, 24547] ⟨245471, 7, [(2, 1), (5, 1), (24547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_24547
  · decide +kernel

theorem prime_254291 : Nat.Prime 254291 := by
  apply nodeValid_prime [2, 5, 59, 431] ⟨254291, 2, [(2, 1), (5, 1), (59, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_431
  · decide +kernel

theorem prime_267811 : Nat.Prime 267811 := by
  apply nodeValid_prime [2, 3, 5, 79, 113] ⟨267811, 10, [(2, 1), (3, 1), (5, 1), (79, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_113
  · decide +kernel

theorem prime_269257 : Nat.Prime 269257 := by
  apply nodeValid_prime [2, 3, 13, 863] ⟨269257, 5, [(2, 3), (3, 1), (13, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_863
  · decide +kernel

theorem prime_279121 : Nat.Prime 279121 := by
  apply nodeValid_prime [2, 3, 5, 1163] ⟨279121, 13, [(2, 4), (3, 1), (5, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1163
  · decide +kernel

theorem prime_322901 : Nat.Prime 322901 := by
  apply nodeValid_prime [2, 5, 3229] ⟨322901, 2, [(2, 2), (5, 2), (3229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3229
  · decide +kernel

theorem prime_360907 : Nat.Prime 360907 := by
  apply nodeValid_prime [2, 3, 7, 13, 661] ⟨360907, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_661
  · decide +kernel

theorem prime_376531 : Nat.Prime 376531 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 163] ⟨376531, 10, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_163
  · decide +kernel

theorem prime_645803 : Nat.Prime 645803 := by
  apply nodeValid_prime [2, 322901] ⟨645803, 2, [(2, 1), (322901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_322901
  · decide +kernel

theorem prime_700897 : Nat.Prime 700897 := by
  apply nodeValid_prime [2, 3, 7, 149] ⟨700897, 15, [(2, 5), (3, 1), (7, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_730277 : Nat.Prime 730277 := by
  apply nodeValid_prime [2, 79, 2311] ⟨730277, 2, [(2, 2), (79, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_2311
  · decide +kernel

theorem prime_912973 : Nat.Prime 912973 := by
  apply nodeValid_prime [2, 3, 76081] ⟨912973, 2, [(2, 2), (3, 1), (76081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76081
  · decide +kernel

theorem prime_997769 : Nat.Prime 997769 := by
  apply nodeValid_prime [2, 124721] ⟨997769, 3, [(2, 3), (124721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_124721
  · decide +kernel

theorem prime_1136299 : Nat.Prime 1136299 := by
  apply nodeValid_prime [2, 3, 229, 827] ⟨1136299, 10, [(2, 1), (3, 1), (229, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_827
  · decide +kernel

theorem prime_1519039 : Nat.Prime 1519039 := by
  apply nodeValid_prime [2, 3, 84391] ⟨1519039, 6, [(2, 1), (3, 2), (84391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_84391
  · decide +kernel

theorem prime_1573939 : Nat.Prime 1573939 := by
  apply nodeValid_prime [2, 3, 29147] ⟨1573939, 2, [(2, 1), (3, 3), (29147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29147
  · decide +kernel

theorem prime_1914791 : Nat.Prime 1914791 := by
  apply nodeValid_prime [2, 5, 43, 61, 73] ⟨1914791, 13, [(2, 1), (5, 1), (43, 1), (61, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_61
    · exact prime_73
  · decide +kernel

theorem prime_2108761 : Nat.Prime 2108761 := by
  apply nodeValid_prime [2, 3, 5, 17573] ⟨2108761, 11, [(2, 3), (3, 1), (5, 1), (17573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17573
  · decide +kernel

theorem prime_2709361 : Nat.Prime 2709361 := by
  apply nodeValid_prime [2, 3, 5, 53, 71] ⟨2709361, 13, [(2, 4), (3, 2), (5, 1), (53, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_71
  · decide +kernel

theorem prime_3473647 : Nat.Prime 3473647 := by
  apply nodeValid_prime [2, 3, 11, 52631] ⟨3473647, 5, [(2, 1), (3, 1), (11, 1), (52631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_52631
  · decide +kernel

theorem prime_4333601 : Nat.Prime 4333601 := by
  apply nodeValid_prime [2, 5, 5417] ⟨4333601, 3, [(2, 5), (5, 2), (5417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5417
  · decide +kernel

theorem prime_4486571 : Nat.Prime 4486571 := by
  apply nodeValid_prime [2, 5, 11, 40787] ⟨4486571, 2, [(2, 1), (5, 1), (11, 1), (40787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_40787
  · decide +kernel

theorem prime_4545197 : Nat.Prime 4545197 := by
  apply nodeValid_prime [2, 1136299] ⟨4545197, 2, [(2, 2), (1136299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1136299
  · decide +kernel

theorem prime_5901347 : Nat.Prime 5901347 := by
  apply nodeValid_prime [2, 11, 17, 31, 509] ⟨5901347, 5, [(2, 1), (11, 1), (17, 1), (31, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_31
    · exact prime_509
  · decide +kernel

theorem prime_6024497 : Nat.Prime 6024497 := by
  apply nodeValid_prime [2, 376531] ⟨6024497, 3, [(2, 4), (376531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_376531
  · decide +kernel

theorem prime_6488429 : Nat.Prime 6488429 := by
  apply nodeValid_prime [2, 79, 20533] ⟨6488429, 2, [(2, 2), (79, 1), (20533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_20533
  · decide +kernel

theorem prime_7649377 : Nat.Prime 7649377 := by
  apply nodeValid_prime [2, 3, 7, 11383] ⟨7649377, 5, [(2, 5), (3, 1), (7, 1), (11383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11383
  · decide +kernel

theorem prime_8571169 : Nat.Prime 8571169 := by
  apply nodeValid_prime [2, 3, 29761] ⟨8571169, 11, [(2, 5), (3, 2), (29761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29761
  · decide +kernel

theorem prime_10275821 : Nat.Prime 10275821 := by
  apply nodeValid_prime [2, 5, 17, 30223] ⟨10275821, 2, [(2, 2), (5, 1), (17, 1), (30223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_30223
  · decide +kernel

theorem prime_11164841 : Nat.Prime 11164841 := by
  apply nodeValid_prime [2, 5, 279121] ⟨11164841, 6, [(2, 3), (5, 1), (279121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_279121
  · decide +kernel

theorem prime_13926173 : Nat.Prime 13926173 := by
  apply nodeValid_prime [2, 13, 267811] ⟨13926173, 2, [(2, 2), (13, 1), (267811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_267811
  · decide +kernel

theorem prime_18740741 : Nat.Prime 18740741 := by
  apply nodeValid_prime [2, 5, 31, 167, 181] ⟨18740741, 3, [(2, 2), (5, 1), (31, 1), (167, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_167
    · exact prime_181
  · decide +kernel

theorem prime_19593641 : Nat.Prime 19593641 := by
  apply nodeValid_prime [2, 5, 11, 44531] ⟨19593641, 6, [(2, 3), (5, 1), (11, 1), (44531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_44531
  · decide +kernel

theorem prime_20557819 : Nat.Prime 20557819 := by
  apply nodeValid_prime [2, 3, 797, 1433] ⟨20557819, 2, [(2, 1), (3, 2), (797, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_797
    · exact prime_1433
  · decide +kernel

theorem prime_20841883 : Nat.Prime 20841883 := by
  apply nodeValid_prime [2, 3, 3473647] ⟨20841883, 3, [(2, 1), (3, 1), (3473647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3473647
  · decide +kernel

theorem prime_22826959 : Nat.Prime 22826959 := by
  apply nodeValid_prime [2, 3, 7, 11, 49409] ⟨22826959, 7, [(2, 1), (3, 1), (7, 1), (11, 1), (49409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_49409
  · decide +kernel

theorem prime_25955297 : Nat.Prime 25955297 := by
  apply nodeValid_prime [2, 41, 73, 271] ⟨25955297, 3, [(2, 5), (41, 1), (73, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_73
    · exact prime_271
  · decide +kernel

theorem prime_32981401 : Nat.Prime 32981401 := by
  apply nodeValid_prime [2, 3, 5, 73, 251] ⟨32981401, 7, [(2, 3), (3, 2), (5, 2), (73, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_251
  · decide +kernel

theorem prime_46828739 : Nat.Prime 46828739 := by
  apply nodeValid_prime [2, 11, 227, 9377] ⟨46828739, 2, [(2, 1), (11, 1), (227, 1), (9377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_227
    · exact prime_9377
  · decide +kernel

theorem prime_75915397 : Nat.Prime 75915397 := by
  apply nodeValid_prime [2, 3, 2108761] ⟨75915397, 2, [(2, 2), (3, 2), (2108761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2108761
  · decide +kernel

theorem prime_122390033 : Nat.Prime 122390033 := by
  apply nodeValid_prime [2, 7649377] ⟨122390033, 3, [(2, 4), (7649377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7649377
  · decide +kernel

theorem prime_127425163 : Nat.Prime 127425163 := by
  apply nodeValid_prime [2, 3, 193, 110039] ⟨127425163, 2, [(2, 1), (3, 1), (193, 1), (110039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_110039
  · decide +kernel

theorem prime_127749703 : Nat.Prime 127749703 := by
  apply nodeValid_prime [2, 3, 1531, 13907] ⟨127749703, 3, [(2, 1), (3, 1), (1531, 1), (13907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1531
    · exact prime_13907
  · decide +kernel

theorem prime_138302893 : Nat.Prime 138302893 := by
  apply nodeValid_prime [2, 3, 7, 13, 37, 163] ⟨138302893, 5, [(2, 2), (3, 2), (7, 2), (13, 1), (37, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_37
    · exact prime_163
  · decide +kernel

theorem prime_141632329 : Nat.Prime 141632329 := by
  apply nodeValid_prime [2, 3, 5901347] ⟨141632329, 14, [(2, 3), (3, 1), (5901347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5901347
  · decide +kernel

theorem prime_152019961 : Nat.Prime 152019961 := by
  apply nodeValid_prime [2, 3, 5, 157, 8069] ⟨152019961, 26, [(2, 3), (3, 1), (5, 1), (157, 1), (8069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
    · exact prime_8069
  · decide +kernel

theorem prime_164676839 : Nat.Prime 164676839 := by
  apply nodeValid_prime [2, 19, 4333601] ⟨164676839, 13, [(2, 1), (19, 1), (4333601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4333601
  · decide +kernel

theorem prime_329353729 : Nat.Prime 329353729 := by
  apply nodeValid_prime [2, 3, 11, 101, 193] ⟨329353729, 14, [(2, 9), (3, 1), (11, 1), (101, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_101
    · exact prime_193
  · decide +kernel

theorem prime_399016873 : Nat.Prime 399016873 := by
  apply nodeValid_prime [2, 3, 19, 31, 97] ⟨399016873, 5, [(2, 3), (3, 2), (19, 1), (31, 1), (97, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_97
  · decide +kernel

theorem prime_417619907 : Nat.Prime 417619907 := by
  apply nodeValid_prime [2, 11, 167, 197, 577] ⟨417619907, 2, [(2, 1), (11, 1), (167, 1), (197, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_167
    · exact prime_197
    · exact prime_577
  · decide +kernel

theorem prime_576666551 : Nat.Prime 576666551 := by
  apply nodeValid_prime [2, 5, 43, 61, 4397] ⟨576666551, 17, [(2, 1), (5, 2), (43, 1), (61, 1), (4397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_61
    · exact prime_4397
  · decide +kernel

theorem prime_848214613 : Nat.Prime 848214613 := by
  apply nodeValid_prime [2, 3, 7, 113, 9929] ⟨848214613, 2, [(2, 2), (3, 3), (7, 1), (113, 1), (9929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
    · exact prime_9929
  · decide +kernel

theorem prime_1229904251 : Nat.Prime 1229904251 := by
  apply nodeValid_prime [2, 5, 1877, 2621] ⟨1229904251, 2, [(2, 1), (5, 3), (1877, 1), (2621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1877
    · exact prime_2621
  · decide +kernel

theorem prime_2005368913 : Nat.Prime 2005368913 := by
  apply nodeValid_prime [2, 3, 13926173] ⟨2005368913, 5, [(2, 4), (3, 2), (13926173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13926173
  · decide +kernel

theorem prime_2305475747 : Nat.Prime 2305475747 := by
  apply nodeValid_prime [2, 7, 164676839] ⟨2305475747, 2, [(2, 1), (7, 1), (164676839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_164676839
  · decide +kernel

theorem prime_2505719443 : Nat.Prime 2505719443 := by
  apply nodeValid_prime [2, 3, 417619907] ⟨2505719443, 3, [(2, 1), (3, 1), (417619907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_417619907
  · decide +kernel

theorem prime_2660349311 : Nat.Prime 2660349311 := by
  apply nodeValid_prime [2, 5, 53, 131, 38317] ⟨2660349311, 7, [(2, 1), (5, 1), (53, 1), (131, 1), (38317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_131
    · exact prime_38317
  · decide +kernel

theorem prime_2700915743 : Nat.Prime 2700915743 := by
  apply nodeValid_prime [2, 7, 43, 4486571] ⟨2700915743, 5, [(2, 1), (7, 1), (43, 1), (4486571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_4486571
  · decide +kernel

theorem prime_4160444503 : Nat.Prime 4160444503 := by
  apply nodeValid_prime [2, 3, 37, 18740741] ⟨4160444503, 5, [(2, 1), (3, 1), (37, 1), (18740741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_18740741
  · decide +kernel

theorem prime_4641800857 : Nat.Prime 4641800857 := by
  apply nodeValid_prime [2, 3, 7, 11, 61, 41177] ⟨4641800857, 13, [(2, 3), (3, 1), (7, 1), (11, 1), (61, 1), (41177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_61
    · exact prime_41177
  · decide +kernel

theorem prime_5036661533 : Nat.Prime 5036661533 := by
  apply nodeValid_prime [2, 7, 23, 163, 47981] ⟨5036661533, 3, [(2, 2), (7, 1), (23, 1), (163, 1), (47981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_163
    · exact prime_47981
  · decide +kernel

theorem prime_5267071457 : Nat.Prime 5267071457 := by
  apply nodeValid_prime [2, 1063, 154841] ⟨5267071457, 3, [(2, 5), (1063, 1), (154841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1063
    · exact prime_154841
  · decide +kernel

theorem prime_5716796341 : Nat.Prime 5716796341 := by
  apply nodeValid_prime [2, 3, 5, 4759, 20021] ⟨5716796341, 2, [(2, 2), (3, 1), (5, 1), (4759, 1), (20021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4759
    · exact prime_20021
  · decide +kernel

theorem prime_9283601777 : Nat.Prime 9283601777 := by
  apply nodeValid_prime [2, 739, 769, 1021] ⟨9283601777, 3, [(2, 4), (739, 1), (769, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_739
    · exact prime_769
    · exact prime_1021
  · decide +kernel

theorem prime_9400796123 : Nat.Prime 9400796123 := by
  apply nodeValid_prime [2, 421, 11164841] ⟨9400796123, 2, [(2, 1), (421, 1), (11164841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_421
    · exact prime_11164841
  · decide +kernel

theorem prime_21553005101 : Nat.Prime 21553005101 := by
  apply nodeValid_prime [2, 5, 11, 19593641] ⟨21553005101, 7, [(2, 2), (5, 2), (11, 1), (19593641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19593641
  · decide +kernel

theorem prime_31843542823 : Nat.Prime 31843542823 := by
  apply nodeValid_prime [2, 3, 7, 13, 19, 673, 4561] ⟨31843542823, 6, [(2, 1), (3, 1), (7, 1), (13, 1), (19, 1), (673, 1), (4561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_673
    · exact prime_4561
  · decide +kernel

theorem prime_32410988917 : Nat.Prime 32410988917 := by
  apply nodeValid_prime [2, 3, 2700915743] ⟨32410988917, 2, [(2, 2), (3, 1), (2700915743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2700915743
  · decide +kernel

theorem prime_124178635831 : Nat.Prime 124178635831 := by
  apply nodeValid_prime [2, 3, 5, 15373, 269257] ⟨124178635831, 6, [(2, 1), (3, 1), (5, 1), (15373, 1), (269257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_15373
    · exact prime_269257
  · decide +kernel

theorem prime_124178654981 : Nat.Prime 124178654981 := by
  apply nodeValid_prime [2, 5, 137, 499, 90823] ⟨124178654981, 2, [(2, 2), (5, 1), (137, 1), (499, 1), (90823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_499
    · exact prime_90823
  · decide +kernel

theorem prime_124178656961 : Nat.Prime 124178656961 := by
  apply nodeValid_prime [2, 5, 17, 22826959] ⟨124178656961, 3, [(2, 6), (5, 1), (17, 1), (22826959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_22826959
  · decide +kernel

theorem prime_124495690339 : Nat.Prime 124495690339 := by
  apply nodeValid_prime [2, 3, 2305475747] ⟨124495690339, 10, [(2, 1), (3, 3), (2305475747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2305475747
  · decide +kernel

theorem prime_124495690483 : Nat.Prime 124495690483 := by
  apply nodeValid_prime [2, 3, 107, 109, 347, 1709] ⟨124495690483, 2, [(2, 1), (3, 2), (107, 1), (109, 1), (347, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_109
    · exact prime_347
    · exact prime_1709
  · decide +kernel

theorem prime_124495709563 : Nat.Prime 124495709563 := by
  apply nodeValid_prime [2, 3, 7, 329353729] ⟨124495709563, 3, [(2, 1), (3, 3), (7, 1), (329353729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_329353729
  · decide +kernel

theorem prime_124813335091 : Nat.Prime 124813335091 := by
  apply nodeValid_prime [2, 3, 5, 4160444503] ⟨124813335091, 11, [(2, 1), (3, 1), (5, 1), (4160444503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4160444503
  · decide +kernel

theorem prime_124813362701 : Nat.Prime 124813362701 := by
  apply nodeValid_prime [2, 5, 13, 61, 1573939] ⟨124813362701, 2, [(2, 2), (5, 2), (13, 1), (61, 1), (1573939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_61
    · exact prime_1573939
  · decide +kernel

theorem prime_124813362979 : Nat.Prime 124813362979 := by
  apply nodeValid_prime [2, 3, 809, 8571169] ⟨124813362979, 2, [(2, 1), (3, 2), (809, 1), (8571169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_809
    · exact prime_8571169
  · decide +kernel

theorem prime_125131510067 : Nat.Prime 125131510067 := by
  apply nodeValid_prime [2, 491, 127425163] ⟨125131510067, 2, [(2, 1), (491, 1), (127425163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_127425163
  · decide +kernel

theorem prime_125131514633 : Nat.Prime 125131514633 := by
  apply nodeValid_prime [2, 31, 43, 1667, 7039] ⟨125131514633, 3, [(2, 3), (31, 1), (43, 1), (1667, 1), (7039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_1667
    · exact prime_7039
  · decide +kernel

theorem prime_125131515281 : Nat.Prime 125131515281 := by
  apply nodeValid_prime [2, 5, 6151, 254291] ⟨125131515281, 6, [(2, 4), (5, 1), (6151, 1), (254291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6151
    · exact prime_254291
  · decide +kernel

theorem prime_125450208347 : Nat.Prime 125450208347 := by
  apply nodeValid_prime [2, 491, 127749703] ⟨125450208347, 2, [(2, 1), (491, 1), (127749703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_127749703
  · decide +kernel

theorem prime_125450209061 : Nat.Prime 125450209061 := by
  apply nodeValid_prime [2, 5, 11, 67, 347, 24527] ⟨125450209061, 2, [(2, 2), (5, 1), (11, 1), (67, 1), (347, 1), (24527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_67
    · exact prime_347
    · exact prime_24527
  · decide +kernel

theorem prime_125450233603 : Nat.Prime 125450233603 := by
  apply nodeValid_prime [2, 3, 17, 1229904251] ⟨125450233603, 2, [(2, 1), (3, 1), (17, 1), (1229904251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1229904251
  · decide +kernel

theorem prime_125769508153 : Nat.Prime 125769508153 := by
  apply nodeValid_prime [2, 3, 37, 141632329] ⟨125769508153, 5, [(2, 3), (3, 1), (37, 1), (141632329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_141632329
  · decide +kernel

theorem prime_125769519503 : Nat.Prime 125769519503 := by
  apply nodeValid_prime [2, 11, 5716796341] ⟨125769519503, 5, [(2, 1), (11, 1), (5716796341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_5716796341
  · decide +kernel

theorem prime_125769519899 : Nat.Prime 125769519899 := by
  apply nodeValid_prime [2, 11, 32533, 175723] ⟨125769519899, 2, [(2, 1), (11, 1), (32533, 1), (175723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_32533
    · exact prime_175723
  · decide +kernel

theorem prime_126089331437 : Nat.Prime 126089331437 := by
  apply nodeValid_prime [2, 877, 5903, 6089] ⟨126089331437, 2, [(2, 2), (877, 1), (5903, 1), (6089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_877
    · exact prime_5903
    · exact prime_6089
  · decide +kernel

theorem prime_126089331869 : Nat.Prime 126089331869 := by
  apply nodeValid_prime [2, 79, 399016873] ⟨126089331869, 2, [(2, 2), (79, 1), (399016873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_399016873
  · decide +kernel

theorem prime_126089334661 : Nat.Prime 126089334661 := by
  apply nodeValid_prime [2, 3, 5, 113, 241, 77167] ⟨126089334661, 6, [(2, 2), (3, 1), (5, 1), (113, 1), (241, 1), (77167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_241
    · exact prime_77167
  · decide +kernel

theorem prime_126409709617 : Nat.Prime 126409709617 := by
  apply nodeValid_prime [2, 3, 29, 3299, 27527] ⟨126409709617, 5, [(2, 4), (3, 1), (29, 1), (3299, 1), (27527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_3299
    · exact prime_27527
  · decide +kernel

theorem prime_126409709929 : Nat.Prime 126409709929 := by
  apply nodeValid_prime [2, 3, 43, 499, 245471] ⟨126409709929, 11, [(2, 3), (3, 1), (43, 1), (499, 1), (245471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_499
    · exact prime_245471
  · decide +kernel

theorem prime_126409714969 : Nat.Prime 126409714969 := by
  apply nodeValid_prime [2, 3, 5267071457] ⟨126409714969, 7, [(2, 3), (3, 1), (5267071457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5267071457
  · decide +kernel

theorem prime_126730631767 : Nat.Prime 126730631767 := by
  apply nodeValid_prime [2, 3, 21169, 997769] ⟨126730631767, 6, [(2, 1), (3, 1), (21169, 1), (997769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21169
    · exact prime_997769
  · decide +kernel

theorem prime_126730632409 : Nat.Prime 126730632409 := by
  apply nodeValid_prime [2, 3, 23, 2531, 90709] ⟨126730632409, 7, [(2, 3), (3, 1), (23, 1), (2531, 1), (90709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2531
    · exact prime_90709
  · decide +kernel

theorem prime_126730646071 : Nat.Prime 126730646071 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 827, 31727] ⟨126730646071, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (827, 1), (31727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_827
    · exact prime_31727
  · decide +kernel

theorem prime_127052118623 : Nat.Prime 127052118623 := by
  apply nodeValid_prime [2, 11, 13, 8221, 54037] ⟨127052118623, 10, [(2, 1), (11, 1), (13, 1), (8221, 1), (54037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_8221
    · exact prime_54037
  · decide +kernel

theorem prime_127052118769 : Nat.Prime 127052118769 := by
  apply nodeValid_prime [2, 3, 127, 20841883] ⟨127052118769, 47, [(2, 4), (3, 1), (127, 1), (20841883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_20841883
  · decide +kernel

theorem prime_127052131907 : Nat.Prime 127052131907 := by
  apply nodeValid_prime [2, 7, 17, 43, 730277] ⟨127052131907, 5, [(2, 1), (7, 1), (17, 2), (43, 1), (730277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_730277
  · decide +kernel

theorem prime_127374170081 : Nat.Prime 127374170081 := by
  apply nodeValid_prime [2, 5, 17, 46828739] ⟨127374170081, 3, [(2, 5), (5, 1), (17, 1), (46828739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_46828739
  · decide +kernel

theorem prime_127374170663 : Nat.Prime 127374170663 := by
  apply nodeValid_prime [2, 1931, 32981401] ⟨127374170663, 5, [(2, 1), (1931, 1), (32981401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1931
    · exact prime_32981401
  · decide +kernel

theorem prime_127374171293 : Nat.Prime 127374171293 := by
  apply nodeValid_prime [2, 31843542823] ⟨127374171293, 2, [(2, 2), (31843542823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31843542823
  · decide +kernel

theorem prime_127696764269 : Nat.Prime 127696764269 := by
  apply nodeValid_prime [2, 439, 2129, 34157] ⟨127696764269, 2, [(2, 2), (439, 1), (2129, 1), (34157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_439
    · exact prime_2129
    · exact prime_34157
  · decide +kernel

theorem prime_127696766929 : Nat.Prime 127696766929 := by
  apply nodeValid_prime [2, 3, 2660349311] ⟨127696766929, 11, [(2, 4), (3, 1), (2660349311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2660349311
  · decide +kernel

theorem prime_127696767241 : Nat.Prime 127696767241 := by
  apply nodeValid_prime [2, 3, 5, 7, 152019961] ⟨127696767241, 17, [(2, 3), (3, 1), (5, 1), (7, 1), (152019961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_152019961
  · decide +kernel

theorem prime_128019908801 : Nat.Prime 128019908801 := by
  apply nodeValid_prime [2, 5, 7, 41, 39827] ⟨128019908801, 3, [(2, 6), (5, 2), (7, 2), (41, 1), (39827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_39827
  · decide +kernel

theorem prime_128019974323 : Nat.Prime 128019974323 := by
  apply nodeValid_prime [2, 3, 37, 576666551] ⟨128019974323, 5, [(2, 1), (3, 1), (37, 1), (576666551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_576666551
  · decide +kernel

theorem prime_128019974519 : Nat.Prime 128019974519 := by
  apply nodeValid_prime [2, 523, 122390033] ⟨128019974519, 13, [(2, 1), (523, 1), (122390033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_523
    · exact prime_122390033
  · decide +kernel

theorem prime_128343604121 : Nat.Prime 128343604121 := by
  apply nodeValid_prime [2, 5, 127, 2287, 11047] ⟨128343604121, 6, [(2, 3), (5, 1), (127, 1), (2287, 1), (11047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_2287
    · exact prime_11047
  · decide +kernel

theorem prime_128343605111 : Nat.Prime 128343605111 := by
  apply nodeValid_prime [2, 5, 7, 17, 71, 1519039] ⟨128343605111, 7, [(2, 1), (5, 1), (7, 1), (17, 1), (71, 1), (1519039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_71
    · exact prime_1519039
  · decide +kernel

theorem prime_128343610433 : Nat.Prime 128343610433 := by
  apply nodeValid_prime [2, 2005368913] ⟨128343610433, 3, [(2, 6), (2005368913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2005368913
  · decide +kernel

theorem prime_128667867673 : Nat.Prime 128667867673 := by
  apply nodeValid_prime [2, 3, 7649, 700897] ⟨128667867673, 5, [(2, 3), (3, 1), (7649, 1), (700897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7649
    · exact prime_700897
  · decide +kernel

theorem prime_128667874787 : Nat.Prime 128667874787 := by
  apply nodeValid_prime [2, 11, 31, 1789, 9587] ⟨128667874787, 5, [(2, 1), (11, 2), (31, 1), (1789, 1), (9587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_1789
    · exact prime_9587
  · decide +kernel

theorem prime_128667874991 : Nat.Prime 128667874991 := by
  apply nodeValid_prime [2, 5, 73, 1847, 95429] ⟨128667874991, 26, [(2, 1), (5, 1), (73, 1), (1847, 1), (95429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_1847
    · exact prime_95429
  · decide +kernel

theorem prime_128992677211 : Nat.Prime 128992677211 := by
  apply nodeValid_prime [2, 3, 5, 23, 2709361] ⟨128992677211, 3, [(2, 1), (3, 2), (5, 1), (23, 2), (2709361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_2709361
  · decide +kernel

theorem prime_128992690861 : Nat.Prime 128992690861 := by
  apply nodeValid_prime [2, 3, 5, 11, 43, 4545197] ⟨128992690861, 22, [(2, 2), (3, 1), (5, 1), (11, 1), (43, 1), (4545197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_4545197
  · decide +kernel

theorem prime_128992691221 : Nat.Prime 128992691221 := by
  apply nodeValid_prime [2, 3, 5, 3329, 645803] ⟨128992691221, 2, [(2, 2), (3, 1), (5, 1), (3329, 1), (645803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3329
    · exact prime_645803
  · decide +kernel

theorem prime_129318030607 : Nat.Prime 129318030607 := by
  apply nodeValid_prime [2, 3, 21553005101] ⟨129318030607, 5, [(2, 1), (3, 1), (21553005101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21553005101
  · decide +kernel

theorem prime_129318030799 : Nat.Prime 129318030799 := by
  apply nodeValid_prime [2, 3, 11, 61, 89, 360907] ⟨129318030799, 3, [(2, 1), (3, 1), (11, 1), (61, 1), (89, 1), (360907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
    · exact prime_89
    · exact prime_360907
  · decide +kernel

theorem prime_129318037777 : Nat.Prime 129318037777 := by
  apply nodeValid_prime [2, 3, 14221, 63149] ⟨129318037777, 5, [(2, 4), (3, 2), (14221, 1), (63149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14221
    · exact prime_63149
  · decide +kernel

theorem prime_129643955359 : Nat.Prime 129643955359 := by
  apply nodeValid_prime [2, 3, 43, 709, 827, 857] ⟨129643955359, 3, [(2, 1), (3, 1), (43, 1), (709, 1), (827, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_709
    · exact prime_827
    · exact prime_857
  · decide +kernel

theorem prime_129643955669 : Nat.Prime 129643955669 := by
  apply nodeValid_prime [2, 32410988917] ⟨129643955669, 2, [(2, 2), (32410988917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32410988917
  · decide +kernel

theorem prime_129643956737 : Nat.Prime 129643956737 := by
  apply nodeValid_prime [2, 7, 19, 881, 2161] ⟨129643956737, 3, [(2, 9), (7, 1), (19, 1), (881, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_881
    · exact prime_2161
  · decide +kernel

theorem prime_129970423997 : Nat.Prime 129970423997 := by
  apply nodeValid_prime [2, 7, 4641800857] ⟨129970423997, 2, [(2, 2), (7, 1), (4641800857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4641800857
  · decide +kernel

theorem prime_129970424879 : Nat.Prime 129970424879 := by
  apply nodeValid_prime [2, 7, 9283601777] ⟨129970424879, 7, [(2, 1), (7, 1), (9283601777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9283601777
  · decide +kernel

theorem prime_129970426583 : Nat.Prime 129970426583 := by
  apply nodeValid_prime [2, 83, 8311, 94207] ⟨129970426583, 5, [(2, 1), (83, 1), (8311, 1), (94207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_8311
    · exact prime_94207
  · decide +kernel

theorem prime_130297410281 : Nat.Prime 130297410281 := by
  apply nodeValid_prime [2, 5, 317, 10275821] ⟨130297410281, 3, [(2, 3), (5, 1), (317, 1), (10275821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_317
    · exact prime_10275821
  · decide +kernel

theorem prime_130297411037 : Nat.Prime 130297411037 := by
  apply nodeValid_prime [2, 13, 2505719443] ⟨130297411037, 2, [(2, 2), (13, 1), (2505719443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2505719443
  · decide +kernel

theorem prime_130297456543 : Nat.Prime 130297456543 := by
  apply nodeValid_prime [2, 3, 11, 83, 2593, 9173] ⟨130297456543, 3, [(2, 1), (3, 1), (11, 1), (83, 1), (2593, 1), (9173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
    · exact prime_2593
    · exact prime_9173
  · decide +kernel

theorem prime_130625048713 : Nat.Prime 130625048713 := by
  apply nodeValid_prime [2, 3, 23, 181, 313, 4177] ⟨130625048713, 7, [(2, 3), (3, 1), (23, 1), (181, 1), (313, 1), (4177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_181
    · exact prime_313
    · exact prime_4177
  · decide +kernel

theorem prime_130625050403 : Nat.Prime 130625050403 := by
  apply nodeValid_prime [2, 7, 11, 848214613] ⟨130625050403, 2, [(2, 1), (7, 1), (11, 1), (848214613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_848214613
  · decide +kernel

theorem prime_130625052629 : Nat.Prime 130625052629 := by
  apply nodeValid_prime [2, 7, 719, 6488429] ⟨130625052629, 2, [(2, 2), (7, 1), (719, 1), (6488429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_719
    · exact prime_6488429
  · decide +kernel

theorem prime_130953195229 : Nat.Prime 130953195229 := by
  apply nodeValid_prime [2, 3, 11953, 912973] ⟨130953195229, 6, [(2, 2), (3, 1), (11953, 1), (912973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11953
    · exact prime_912973
  · decide +kernel

theorem prime_130953199859 : Nat.Prime 130953199859 := by
  apply nodeValid_prime [2, 13, 5036661533] ⟨130953199859, 2, [(2, 1), (13, 1), (5036661533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5036661533
  · decide +kernel

theorem prime_130953200437 : Nat.Prime 130953200437 := by
  apply nodeValid_prime [2, 3, 17041, 213461] ⟨130953200437, 2, [(2, 2), (3, 2), (17041, 1), (213461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17041
    · exact prime_213461
  · decide +kernel

theorem prime_131281892227 : Nat.Prime 131281892227 := by
  apply nodeValid_prime [2, 3, 281, 25955297] ⟨131281892227, 3, [(2, 1), (3, 2), (281, 1), (25955297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_25955297
  · decide +kernel

theorem prime_131281900543 : Nat.Prime 131281900543 := by
  apply nodeValid_prime [2, 3, 13, 293, 1914791] ⟨131281900543, 3, [(2, 1), (3, 2), (13, 1), (293, 1), (1914791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_293
    · exact prime_1914791
  · decide +kernel

theorem prime_131281900777 : Nat.Prime 131281900777 := by
  apply nodeValid_prime [2, 3, 13, 71, 347, 5693] ⟨131281900777, 5, [(2, 3), (3, 2), (13, 1), (71, 1), (347, 1), (5693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_347
    · exact prime_5693
  · decide +kernel

theorem prime_131611145723 : Nat.Prime 131611145723 := by
  apply nodeValid_prime [2, 7, 9400796123] ⟨131611145723, 2, [(2, 1), (7, 1), (9400796123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9400796123
  · decide +kernel

theorem prime_131611157239 : Nat.Prime 131611157239 := by
  apply nodeValid_prime [2, 3, 11, 97, 20557819] ⟨131611157239, 3, [(2, 1), (3, 1), (11, 1), (97, 1), (20557819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_20557819
  · decide +kernel

theorem prime_131611161463 : Nat.Prime 131611161463 := by
  apply nodeValid_prime [2, 3, 11, 331, 6024497] ⟨131611161463, 5, [(2, 1), (3, 1), (11, 1), (331, 1), (6024497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_331
    · exact prime_6024497
  · decide +kernel

theorem prime_131940959681 : Nat.Prime 131940959681 := by
  apply nodeValid_prime [2, 5, 109, 769, 4919] ⟨131940959681, 3, [(2, 6), (5, 1), (109, 1), (769, 1), (4919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_769
    · exact prime_4919
  · decide +kernel

theorem prime_131940959923 : Nat.Prime 131940959923 := by
  apply nodeValid_prime [2, 3, 53, 138302893] ⟨131940959923, 2, [(2, 1), (3, 2), (53, 1), (138302893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_138302893
  · decide +kernel

theorem prime_131940959987 : Nat.Prime 131940959987 := by
  apply nodeValid_prime [2, 11, 79, 75915397] ⟨131940959987, 2, [(2, 1), (11, 1), (79, 1), (75915397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79
    · exact prime_75915397
  · decide +kernel

end Sude.Lucas.Generated
