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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3581 : Nat.Prime 3581 := by
  apply nodeValid_prime [2, 5, 179] ⟨3581, 2, [(2, 2), (5, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
  · decide +kernel

theorem prime_4409 : Nat.Prime 4409 := by
  apply nodeValid_prime [2, 19, 29] ⟨4409, 3, [(2, 3), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_8819 : Nat.Prime 8819 := by
  apply nodeValid_prime [2, 4409] ⟨8819, 2, [(2, 1), (4409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4409
  · decide +kernel

theorem prime_10343 : Nat.Prime 10343 := by
  apply nodeValid_prime [2, 5171] ⟨10343, 5, [(2, 1), (5171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5171
  · decide +kernel

theorem prime_10399 : Nat.Prime 10399 := by
  apply nodeValid_prime [2, 3, 1733] ⟨10399, 6, [(2, 1), (3, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1733
  · decide +kernel

theorem prime_11299 : Nat.Prime 11299 := by
  apply nodeValid_prime [2, 3, 7, 269] ⟨11299, 3, [(2, 1), (3, 1), (7, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_269
  · decide +kernel

theorem prime_13171 : Nat.Prime 13171 := by
  apply nodeValid_prime [2, 3, 5, 439] ⟨13171, 11, [(2, 1), (3, 1), (5, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_13553 : Nat.Prime 13553 := by
  apply nodeValid_prime [2, 7, 11] ⟨13553, 3, [(2, 4), (7, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_14621 : Nat.Prime 14621 := by
  apply nodeValid_prime [2, 5, 17, 43] ⟨14621, 2, [(2, 2), (5, 1), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_15017 : Nat.Prime 15017 := by
  apply nodeValid_prime [2, 1877] ⟨15017, 3, [(2, 3), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1877
  · decide +kernel

theorem prime_19381 : Nat.Prime 19381 := by
  apply nodeValid_prime [2, 3, 5, 17, 19] ⟨19381, 7, [(2, 2), (3, 1), (5, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_21023 : Nat.Prime 21023 := by
  apply nodeValid_prime [2, 23, 457] ⟨21023, 5, [(2, 1), (23, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_457
  · decide +kernel

theorem prime_21977 : Nat.Prime 21977 := by
  apply nodeValid_prime [2, 41, 67] ⟨21977, 3, [(2, 3), (41, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_67
  · decide +kernel

theorem prime_23167 : Nat.Prime 23167 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨23167, 3, [(2, 1), (3, 4), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_23831 : Nat.Prime 23831 := by
  apply nodeValid_prime [2, 5, 2383] ⟨23831, 11, [(2, 1), (5, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2383
  · decide +kernel

theorem prime_24151 : Nat.Prime 24151 := by
  apply nodeValid_prime [2, 3, 5, 7, 23] ⟨24151, 6, [(2, 1), (3, 1), (5, 2), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_24551 : Nat.Prime 24551 := by
  apply nodeValid_prime [2, 5, 491] ⟨24551, 7, [(2, 1), (5, 2), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_491
  · decide +kernel

theorem prime_25321 : Nat.Prime 25321 := by
  apply nodeValid_prime [2, 3, 5, 211] ⟨25321, 19, [(2, 3), (3, 1), (5, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_211
  · decide +kernel

theorem prime_32009 : Nat.Prime 32009 := by
  apply nodeValid_prime [2, 4001] ⟨32009, 3, [(2, 3), (4001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4001
  · decide +kernel

theorem prime_33529 : Nat.Prime 33529 := by
  apply nodeValid_prime [2, 3, 11, 127] ⟨33529, 7, [(2, 3), (3, 1), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_33637 : Nat.Prime 33637 := by
  apply nodeValid_prime [2, 3, 2803] ⟨33637, 2, [(2, 2), (3, 1), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2803
  · decide +kernel

theorem prime_33713 : Nat.Prime 33713 := by
  apply nodeValid_prime [2, 7, 43] ⟨33713, 3, [(2, 4), (7, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_37861 : Nat.Prime 37861 := by
  apply nodeValid_prime [2, 3, 5, 631] ⟨37861, 2, [(2, 2), (3, 1), (5, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_631
  · decide +kernel

theorem prime_39863 : Nat.Prime 39863 := by
  apply nodeValid_prime [2, 19, 1049] ⟨39863, 5, [(2, 1), (19, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1049
  · decide +kernel

theorem prime_42649 : Nat.Prime 42649 := by
  apply nodeValid_prime [2, 3, 1777] ⟨42649, 11, [(2, 3), (3, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1777
  · decide +kernel

theorem prime_46181 : Nat.Prime 46181 := by
  apply nodeValid_prime [2, 5, 2309] ⟨46181, 2, [(2, 2), (5, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2309
  · decide +kernel

theorem prime_49103 : Nat.Prime 49103 := by
  apply nodeValid_prime [2, 24551] ⟨49103, 5, [(2, 1), (24551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24551
  · decide +kernel

theorem prime_51307 : Nat.Prime 51307 := by
  apply nodeValid_prime [2, 3, 17, 503] ⟨51307, 5, [(2, 1), (3, 1), (17, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_503
  · decide +kernel

theorem prime_55579 : Nat.Prime 55579 := by
  apply nodeValid_prime [2, 3, 59, 157] ⟨55579, 2, [(2, 1), (3, 1), (59, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_157
  · decide +kernel

theorem prime_59011 : Nat.Prime 59011 := by
  apply nodeValid_prime [2, 3, 5, 7, 281] ⟨59011, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_281
  · decide +kernel

theorem prime_60077 : Nat.Prime 60077 := by
  apply nodeValid_prime [2, 23, 653] ⟨60077, 2, [(2, 2), (23, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_653
  · decide +kernel

theorem prime_63727 : Nat.Prime 63727 := by
  apply nodeValid_prime [2, 3, 13, 19, 43] ⟨63727, 6, [(2, 1), (3, 1), (13, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_64019 : Nat.Prime 64019 := by
  apply nodeValid_prime [2, 32009] ⟨64019, 2, [(2, 1), (32009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32009
  · decide +kernel

theorem prime_80177 : Nat.Prime 80177 := by
  apply nodeValid_prime [2, 5011] ⟨80177, 3, [(2, 4), (5011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5011
  · decide +kernel

theorem prime_97441 : Nat.Prime 97441 := by
  apply nodeValid_prime [2, 3, 5, 7, 29] ⟨97441, 37, [(2, 5), (3, 1), (5, 1), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_107269 : Nat.Prime 107269 := by
  apply nodeValid_prime [2, 3, 7, 1277] ⟨107269, 6, [(2, 2), (3, 1), (7, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1277
  · decide +kernel

theorem prime_121267 : Nat.Prime 121267 := by
  apply nodeValid_prime [2, 3, 6737] ⟨121267, 3, [(2, 1), (3, 2), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6737
  · decide +kernel

theorem prime_122777 : Nat.Prime 122777 := by
  apply nodeValid_prime [2, 103, 149] ⟨122777, 3, [(2, 3), (103, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_149
  · decide +kernel

theorem prime_131711 : Nat.Prime 131711 := by
  apply nodeValid_prime [2, 5, 13171] ⟨131711, 13, [(2, 1), (5, 1), (13171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13171
  · decide +kernel

theorem prime_135389 : Nat.Prime 135389 := by
  apply nodeValid_prime [2, 11, 17, 181] ⟨135389, 2, [(2, 2), (11, 1), (17, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_181
  · decide +kernel

theorem prime_147397 : Nat.Prime 147397 := by
  apply nodeValid_prime [2, 3, 71, 173] ⟨147397, 2, [(2, 2), (3, 1), (71, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_173
  · decide +kernel

theorem prime_148609 : Nat.Prime 148609 := by
  apply nodeValid_prime [2, 3, 43] ⟨148609, 7, [(2, 7), (3, 3), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel

theorem prime_150827 : Nat.Prime 150827 := by
  apply nodeValid_prime [2, 13, 5801] ⟨150827, 2, [(2, 1), (13, 1), (5801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5801
  · decide +kernel

theorem prime_192917 : Nat.Prime 192917 := by
  apply nodeValid_prime [2, 17, 2837] ⟨192917, 2, [(2, 2), (17, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2837
  · decide +kernel

theorem prime_193871 : Nat.Prime 193871 := by
  apply nodeValid_prime [2, 5, 19387] ⟨193871, 13, [(2, 1), (5, 1), (19387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19387
  · decide +kernel

theorem prime_203221 : Nat.Prime 203221 := by
  apply nodeValid_prime [2, 3, 5, 1129] ⟨203221, 2, [(2, 2), (3, 2), (5, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1129
  · decide +kernel

theorem prime_215893 : Nat.Prime 215893 := by
  apply nodeValid_prime [2, 3, 1999] ⟨215893, 2, [(2, 2), (3, 3), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1999
  · decide +kernel

theorem prime_270307 : Nat.Prime 270307 := by
  apply nodeValid_prime [2, 3, 15017] ⟨270307, 3, [(2, 1), (3, 2), (15017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15017
  · decide +kernel

theorem prime_281381 : Nat.Prime 281381 := by
  apply nodeValid_prime [2, 5, 11, 1279] ⟨281381, 2, [(2, 2), (5, 1), (11, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1279
  · decide +kernel

theorem prime_295187 : Nat.Prime 295187 := by
  apply nodeValid_prime [2, 37, 3989] ⟨295187, 5, [(2, 1), (37, 1), (3989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_3989
  · decide +kernel

theorem prime_326309 : Nat.Prime 326309 := by
  apply nodeValid_prime [2, 29, 97] ⟨326309, 2, [(2, 2), (29, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_97
  · decide +kernel

theorem prime_326737 : Nat.Prime 326737 := by
  apply nodeValid_prime [2, 3, 2269] ⟨326737, 5, [(2, 4), (3, 2), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2269
  · decide +kernel

theorem prime_699287 : Nat.Prime 699287 := by
  apply nodeValid_prime [2, 7, 199, 251] ⟨699287, 5, [(2, 1), (7, 1), (199, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_199
    · exact prime_251
  · decide +kernel

theorem prime_803669 : Nat.Prime 803669 := by
  apply nodeValid_prime [2, 331, 607] ⟨803669, 2, [(2, 2), (331, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_607
  · decide +kernel

theorem prime_814579 : Nat.Prime 814579 := by
  apply nodeValid_prime [2, 3, 127, 1069] ⟨814579, 2, [(2, 1), (3, 1), (127, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_1069
  · decide +kernel

theorem prime_841079 : Nat.Prime 841079 := by
  apply nodeValid_prime [2, 7, 60077] ⟨841079, 7, [(2, 1), (7, 1), (60077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_60077
  · decide +kernel

theorem prime_956713 : Nat.Prime 956713 := by
  apply nodeValid_prime [2, 3, 39863] ⟨956713, 10, [(2, 3), (3, 1), (39863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39863
  · decide +kernel

theorem prime_974411 : Nat.Prime 974411 := by
  apply nodeValid_prime [2, 5, 97441] ⟨974411, 7, [(2, 1), (5, 1), (97441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97441
  · decide +kernel

theorem prime_1069499 : Nat.Prime 1069499 := by
  apply nodeValid_prime [2, 661, 809] ⟨1069499, 2, [(2, 1), (661, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_661
    · exact prime_809
  · decide +kernel

theorem prime_1152343 : Nat.Prime 1152343 := by
  apply nodeValid_prime [2, 3, 64019] ⟨1152343, 3, [(2, 1), (3, 2), (64019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_64019
  · decide +kernel

theorem prime_1157503 : Nat.Prime 1157503 := by
  apply nodeValid_prime [2, 3, 192917] ⟨1157503, 3, [(2, 1), (3, 1), (192917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_192917
  · decide +kernel

theorem prime_1573577 : Nat.Prime 1573577 := by
  apply nodeValid_prime [2, 239, 823] ⟨1573577, 3, [(2, 3), (239, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_823
  · decide +kernel

theorem prime_1682159 : Nat.Prime 1682159 := by
  apply nodeValid_prime [2, 841079] ⟨1682159, 13, [(2, 1), (841079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_841079
  · decide +kernel

theorem prime_1760797 : Nat.Prime 1760797 := by
  apply nodeValid_prime [2, 3, 59, 829] ⟨1760797, 2, [(2, 2), (3, 2), (59, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_829
  · decide +kernel

theorem prime_1814927 : Nat.Prime 1814927 := by
  apply nodeValid_prime [2, 31, 73, 401] ⟨1814927, 5, [(2, 1), (31, 1), (73, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_73
    · exact prime_401
  · decide +kernel

theorem prime_2138999 : Nat.Prime 2138999 := by
  apply nodeValid_prime [2, 1069499] ⟨2138999, 7, [(2, 1), (1069499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1069499
  · decide +kernel

theorem prime_2259949 : Nat.Prime 2259949 := by
  apply nodeValid_prime [2, 3, 47, 4007] ⟨2259949, 6, [(2, 2), (3, 1), (47, 1), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_4007
  · decide +kernel

theorem prime_2677681 : Nat.Prime 2677681 := by
  apply nodeValid_prime [2, 3, 5, 3719] ⟨2677681, 11, [(2, 4), (3, 2), (5, 1), (3719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3719
  · decide +kernel

theorem prime_3829373 : Nat.Prime 3829373 := by
  apply nodeValid_prime [2, 47, 20369] ⟨3829373, 2, [(2, 2), (47, 1), (20369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_20369
  · decide +kernel

theorem prime_4214753 : Nat.Prime 4214753 := by
  apply nodeValid_prime [2, 131711] ⟨4214753, 3, [(2, 5), (131711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_131711
  · decide +kernel

theorem prime_4264901 : Nat.Prime 4264901 := by
  apply nodeValid_prime [2, 5, 42649] ⟨4264901, 2, [(2, 2), (5, 2), (42649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_42649
  · decide +kernel

theorem prime_6117091 : Nat.Prime 6117091 := by
  apply nodeValid_prime [2, 3, 5, 7, 29129] ⟨6117091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (29129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29129
  · decide +kernel

theorem prime_7043189 : Nat.Prime 7043189 := by
  apply nodeValid_prime [2, 1760797] ⟨7043189, 2, [(2, 2), (1760797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1760797
  · decide +kernel

theorem prime_10328971 : Nat.Prime 10328971 := by
  apply nodeValid_prime [2, 3, 5, 19, 18121] ⟨10328971, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (18121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_18121
  · decide +kernel

theorem prime_14298931 : Nat.Prime 14298931 := by
  apply nodeValid_prime [2, 3, 5, 127, 139] ⟨14298931, 10, [(2, 1), (3, 4), (5, 1), (127, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
    · exact prime_139
  · decide +kernel

theorem prime_20031169 : Nat.Prime 20031169 := by
  apply nodeValid_prime [2, 3, 17, 19] ⟨20031169, 13, [(2, 6), (3, 1), (17, 2), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_20814127 : Nat.Prime 20814127 := by
  apply nodeValid_prime [2, 3, 23, 150827] ⟨20814127, 3, [(2, 1), (3, 1), (23, 1), (150827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_150827
  · decide +kernel

theorem prime_22577903 : Nat.Prime 22577903 := by
  apply nodeValid_prime [2, 347, 32533] ⟨22577903, 5, [(2, 1), (347, 1), (32533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_32533
  · decide +kernel

theorem prime_25288519 : Nat.Prime 25288519 := by
  apply nodeValid_prime [2, 3, 4214753] ⟨25288519, 3, [(2, 1), (3, 1), (4214753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4214753
  · decide +kernel

theorem prime_30675527 : Nat.Prime 30675527 := by
  apply nodeValid_prime [2, 7, 499, 4391] ⟨30675527, 5, [(2, 1), (7, 1), (499, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_499
    · exact prime_4391
  · decide +kernel

theorem prime_34630181 : Nat.Prime 34630181 := by
  apply nodeValid_prime [2, 5, 13, 23, 5791] ⟨34630181, 7, [(2, 2), (5, 1), (13, 1), (23, 1), (5791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_5791
  · decide +kernel

theorem prime_40681573 : Nat.Prime 40681573 := by
  apply nodeValid_prime [2, 3, 23, 147397] ⟨40681573, 2, [(2, 2), (3, 1), (23, 1), (147397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_147397
  · decide +kernel

theorem prime_43895219 : Nat.Prime 43895219 := by
  apply nodeValid_prime [2, 131, 239, 701] ⟨43895219, 2, [(2, 1), (131, 1), (239, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_239
    · exact prime_701
  · decide +kernel

theorem prime_46902593 : Nat.Prime 46902593 := by
  apply nodeValid_prime [2, 11, 17, 3919] ⟨46902593, 3, [(2, 6), (11, 1), (17, 1), (3919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_3919
  · decide +kernel

theorem prime_91178651 : Nat.Prime 91178651 := by
  apply nodeValid_prime [2, 5, 17, 107269] ⟨91178651, 2, [(2, 1), (5, 2), (17, 1), (107269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_107269
  · decide +kernel

theorem prime_105384451 : Nat.Prime 105384451 := by
  apply nodeValid_prime [2, 3, 5, 19, 103, 359] ⟨105384451, 7, [(2, 1), (3, 1), (5, 2), (19, 1), (103, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_103
    · exact prime_359
  · decide +kernel

theorem prime_110680831 : Nat.Prime 110680831 := by
  apply nodeValid_prime [2, 3, 5, 13, 23, 457] ⟨110680831, 6, [(2, 1), (3, 4), (5, 1), (13, 1), (23, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_457
  · decide +kernel

theorem prime_136887869 : Nat.Prime 136887869 := by
  apply nodeValid_prime [2, 13, 109, 24151] ⟨136887869, 2, [(2, 2), (13, 1), (109, 1), (24151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_109
    · exact prime_24151
  · decide +kernel

theorem prime_181849253 : Nat.Prime 181849253 := by
  apply nodeValid_prime [2, 13, 139, 181] ⟨181849253, 2, [(2, 2), (13, 1), (139, 2), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_139
    · exact prime_181
  · decide +kernel

theorem prime_220840271 : Nat.Prime 220840271 := by
  apply nodeValid_prime [2, 5, 7, 881, 3581] ⟨220840271, 7, [(2, 1), (5, 1), (7, 1), (881, 1), (3581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_881
    · exact prime_3581
  · decide +kernel

theorem prime_230297239 : Nat.Prime 230297239 := by
  apply nodeValid_prime [2, 3, 1237, 10343] ⟨230297239, 3, [(2, 1), (3, 2), (1237, 1), (10343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1237
    · exact prime_10343
  · decide +kernel

theorem prime_362855609 : Nat.Prime 362855609 := by
  apply nodeValid_prime [2, 139, 326309] ⟨362855609, 3, [(2, 3), (139, 1), (326309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_326309
  · decide +kernel

theorem prime_417653893 : Nat.Prime 417653893 := by
  apply nodeValid_prime [2, 3, 17, 421, 1621] ⟨417653893, 5, [(2, 2), (3, 2), (17, 1), (421, 1), (1621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_421
    · exact prime_1621
  · decide +kernel

theorem prime_503188177 : Nat.Prime 503188177 := by
  apply nodeValid_prime [2, 3, 227, 46181] ⟨503188177, 5, [(2, 4), (3, 1), (227, 1), (46181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_46181
  · decide +kernel

theorem prime_528011461 : Nat.Prime 528011461 := by
  apply nodeValid_prime [2, 3, 5, 23, 37, 383] ⟨528011461, 10, [(2, 2), (3, 4), (5, 1), (23, 1), (37, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_383
  · decide +kernel

theorem prime_603292849 : Nat.Prime 603292849 := by
  apply nodeValid_prime [2, 3, 2707, 4643] ⟨603292849, 7, [(2, 4), (3, 1), (2707, 1), (4643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2707
    · exact prime_4643
  · decide +kernel

theorem prime_1201870141 : Nat.Prime 1201870141 := by
  apply nodeValid_prime [2, 3, 5, 20031169] ⟨1201870141, 2, [(2, 2), (3, 1), (5, 1), (20031169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20031169
  · decide +kernel

theorem prime_1404491287 : Nat.Prime 1404491287 := by
  apply nodeValid_prime [2, 3, 11, 19, 29, 3511] ⟨1404491287, 5, [(2, 1), (3, 1), (11, 2), (19, 1), (29, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_29
    · exact prime_3511
  · decide +kernel

theorem prime_1621178941 : Nat.Prime 1621178941 := by
  apply nodeValid_prime [2, 3, 5, 337, 80177] ⟨1621178941, 2, [(2, 2), (3, 1), (5, 1), (337, 1), (80177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_337
    · exact prime_80177
  · decide +kernel

theorem prime_3846940703 : Nat.Prime 3846940703 := by
  apply nodeValid_prime [2, 11, 41, 4264901] ⟨3846940703, 5, [(2, 1), (11, 1), (41, 1), (4264901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_4264901
  · decide +kernel

theorem prime_4145350303 : Nat.Prime 4145350303 := by
  apply nodeValid_prime [2, 3, 230297239] ⟨4145350303, 5, [(2, 1), (3, 2), (230297239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_230297239
  · decide +kernel

theorem prime_5170339813 : Nat.Prime 5170339813 := by
  apply nodeValid_prime [2, 3, 11, 17, 19, 121267] ⟨5170339813, 6, [(2, 2), (3, 1), (11, 1), (17, 1), (19, 1), (121267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_121267
  · decide +kernel

theorem prime_7970681981 : Nat.Prime 7970681981 := by
  apply nodeValid_prime [2, 5, 409, 974411] ⟨7970681981, 2, [(2, 2), (5, 1), (409, 1), (974411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
    · exact prime_974411
  · decide +kernel

theorem prime_8097913427 : Nat.Prime 8097913427 := by
  apply nodeValid_prime [2, 29, 83, 1682159] ⟨8097913427, 2, [(2, 1), (29, 1), (83, 1), (1682159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_83
    · exact prime_1682159
  · decide +kernel

theorem prime_9241472389 : Nat.Prime 9241472389 := by
  apply nodeValid_prime [2, 3, 37, 20814127] ⟨9241472389, 10, [(2, 2), (3, 1), (37, 1), (20814127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_20814127
  · decide +kernel

theorem prime_13090208419 : Nat.Prime 13090208419 := by
  apply nodeValid_prime [2, 3, 7, 34630181] ⟨13090208419, 2, [(2, 1), (3, 3), (7, 1), (34630181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_34630181
  · decide +kernel

theorem prime_17753220613 : Nat.Prime 17753220613 := by
  apply nodeValid_prime [2, 3, 359, 641, 2143] ⟨17753220613, 2, [(2, 2), (3, 2), (359, 1), (641, 1), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_641
    · exact prime_2143
  · decide +kernel

theorem prime_19573313707 : Nat.Prime 19573313707 := by
  apply nodeValid_prime [2, 3, 43, 25288519] ⟨19573313707, 2, [(2, 1), (3, 2), (43, 1), (25288519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_25288519
  · decide +kernel

theorem prime_20681359253 : Nat.Prime 20681359253 := by
  apply nodeValid_prime [2, 5170339813] ⟨20681359253, 2, [(2, 2), (5170339813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5170339813
  · decide +kernel

theorem prime_39332721569 : Nat.Prime 39332721569 := by
  apply nodeValid_prime [2, 7, 17, 10328971] ⟨39332721569, 3, [(2, 5), (7, 1), (17, 1), (10328971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_10328971
  · decide +kernel

theorem prime_44383051513 : Nat.Prime 44383051513 := by
  apply nodeValid_prime [2, 3, 17, 569, 63727] ⟨44383051513, 7, [(2, 3), (3, 2), (17, 1), (569, 1), (63727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_569
    · exact prime_63727
  · decide +kernel

theorem prime_54545589013 : Nat.Prime 54545589013 := by
  apply nodeValid_prime [2, 3, 1187, 3829373] ⟨54545589013, 5, [(2, 2), (3, 1), (1187, 1), (3829373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1187
    · exact prime_3829373
  · decide +kernel

theorem prime_67107486671 : Nat.Prime 67107486671 := by
  apply nodeValid_prime [2, 5, 7, 25321, 37861] ⟨67107486671, 11, [(2, 1), (5, 1), (7, 1), (25321, 1), (37861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_25321
    · exact prime_37861
  · decide +kernel

theorem prime_530049643553 : Nat.Prime 530049643553 := by
  apply nodeValid_prime [2, 11, 13, 163, 199, 3571] ⟨530049643553, 5, [(2, 5), (11, 1), (13, 1), (163, 1), (199, 1), (3571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_163
    · exact prime_199
    · exact prime_3571
  · decide +kernel

theorem prime_530049698201 : Nat.Prime 530049698201 := by
  apply nodeValid_prime [2, 5, 11, 29, 613, 13553] ⟨530049698201, 3, [(2, 3), (5, 2), (11, 1), (29, 1), (613, 1), (13553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_613
    · exact prime_13553
  · decide +kernel

theorem prime_530049698951 : Nat.Prime 530049698951 := by
  apply nodeValid_prime [2, 5, 49103, 215893] ⟨530049698951, 11, [(2, 1), (5, 2), (49103, 1), (215893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49103
    · exact prime_215893
  · decide +kernel

theorem prime_530897706487 : Nat.Prime 530897706487 := by
  apply nodeValid_prime [2, 3, 7, 1404491287] ⟨530897706487, 3, [(2, 1), (3, 3), (7, 1), (1404491287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1404491287
  · decide +kernel

theorem prime_530897707121 : Nat.Prime 530897707121 := by
  apply nodeValid_prime [2, 5, 11, 603292849] ⟨530897707121, 6, [(2, 4), (5, 1), (11, 1), (603292849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_603292849
  · decide +kernel

theorem prime_530897710121 : Nat.Prime 530897710121 := by
  apply nodeValid_prime [2, 5, 37, 47, 149, 181, 283] ⟨530897710121, 3, [(2, 3), (5, 1), (37, 1), (47, 1), (149, 1), (181, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_47
    · exact prime_149
    · exact prime_181
    · exact prime_283
  · decide +kernel

theorem prime_531746682967 : Nat.Prime 531746682967 := by
  apply nodeValid_prime [2, 3, 673, 43895219] ⟨531746682967, 3, [(2, 1), (3, 2), (673, 1), (43895219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_673
    · exact prime_43895219
  · decide +kernel

theorem prime_531746683123 : Nat.Prime 531746683123 := by
  apply nodeValid_prime [2, 3, 12583, 7043189] ⟨531746683123, 3, [(2, 1), (3, 1), (12583, 1), (7043189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12583
    · exact prime_7043189
  · decide +kernel

theorem prime_531746692649 : Nat.Prime 531746692649 := by
  apply nodeValid_prime [2, 41, 1621178941] ⟨531746692649, 3, [(2, 3), (41, 1), (1621178941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1621178941
  · decide +kernel

theorem prime_532596591853 : Nat.Prime 532596591853 := by
  apply nodeValid_prime [2, 3, 13, 73, 223, 401, 523] ⟨532596591853, 5, [(2, 2), (3, 1), (13, 1), (73, 1), (223, 1), (401, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_223
    · exact prime_401
    · exact prime_523
  · decide +kernel

theorem prime_532596618157 : Nat.Prime 532596618157 := by
  apply nodeValid_prime [2, 3, 44383051513] ⟨532596618157, 2, [(2, 2), (3, 1), (44383051513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44383051513
  · decide +kernel

theorem prime_532596618391 : Nat.Prime 532596618391 := by
  apply nodeValid_prime [2, 3, 5, 17753220613] ⟨532596618391, 3, [(2, 1), (3, 1), (5, 1), (17753220613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17753220613
  · decide +kernel

theorem prime_533447401757 : Nat.Prime 533447401757 := by
  apply nodeValid_prime [2, 59011, 2259949] ⟨533447401757, 2, [(2, 2), (59011, 1), (2259949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59011
    · exact prime_2259949
  · decide +kernel

theorem prime_533447402603 : Nat.Prime 533447402603 := by
  apply nodeValid_prime [2, 409, 3209, 203221] ⟨533447402603, 2, [(2, 1), (409, 1), (3209, 1), (203221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_3209
    · exact prime_203221
  · decide +kernel

theorem prime_533447414531 : Nat.Prime 533447414531 := by
  apply nodeValid_prime [2, 5, 37, 47, 30675527] ⟨533447414531, 2, [(2, 1), (5, 1), (37, 1), (47, 1), (30675527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_47
    · exact prime_30675527
  · decide +kernel

theorem prime_534299156689 : Nat.Prime 534299156689 := by
  apply nodeValid_prime [2, 3, 11, 331, 541, 5651] ⟨534299156689, 31, [(2, 4), (3, 1), (11, 1), (331, 1), (541, 1), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_331
    · exact prime_541
    · exact prime_5651
  · decide +kernel

theorem prime_534299166571 : Nat.Prime 534299166571 := by
  apply nodeValid_prime [2, 3, 5, 13, 105384451] ⟨534299166571, 12, [(2, 1), (3, 1), (5, 1), (13, 2), (105384451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_105384451
  · decide +kernel

theorem prime_534299166587 : Nat.Prime 534299166587 := by
  apply nodeValid_prime [2, 379, 21023, 33529] ⟨534299166587, 2, [(2, 1), (379, 1), (21023, 1), (33529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_21023
    · exact prime_33529
  · decide +kernel

theorem prime_535151790977 : Nat.Prime 535151790977 := by
  apply nodeValid_prime [2, 11, 271, 947, 1481] ⟨535151790977, 3, [(2, 7), (11, 1), (271, 1), (947, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_271
    · exact prime_947
    · exact prime_1481
  · decide +kernel

theorem prime_535151791607 : Nat.Prime 535151791607 := by
  apply nodeValid_prime [2, 18713, 14298931] ⟨535151791607, 5, [(2, 1), (18713, 1), (14298931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18713
    · exact prime_14298931
  · decide +kernel

theorem prime_535151817581 : Nat.Prime 535151817581 := by
  apply nodeValid_prime [2, 5, 83, 14669, 21977] ⟨535151817581, 3, [(2, 2), (5, 1), (83, 1), (14669, 1), (21977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_14669
    · exact prime_21977
  · decide +kernel

theorem prime_536005398563 : Nat.Prime 536005398563 := by
  apply nodeValid_prime [2, 29, 9241472389] ⟨536005398563, 5, [(2, 1), (29, 1), (9241472389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_9241472389
  · decide +kernel

theorem prime_536005432213 : Nat.Prime 536005432213 := by
  apply nodeValid_prime [2, 3, 55579, 803669] ⟨536005432213, 5, [(2, 2), (3, 1), (55579, 1), (803669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55579
    · exact prime_803669
  · decide +kernel

theorem prime_536005432393 : Nat.Prime 536005432393 := by
  apply nodeValid_prime [2, 3, 19381, 1152343] ⟨536005432393, 5, [(2, 3), (3, 1), (19381, 1), (1152343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19381
    · exact prime_1152343
  · decide +kernel

theorem prime_536859893369 : Nat.Prime 536859893369 := by
  apply nodeValid_prime [2, 67107486671] ⟨536859893369, 3, [(2, 3), (67107486671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67107486671
  · decide +kernel

theorem prime_536859897089 : Nat.Prime 536859897089 := by
  apply nodeValid_prime [2, 23, 91178651] ⟨536859897089, 3, [(2, 8), (23, 1), (91178651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_91178651
  · decide +kernel

theorem prime_536859905969 : Nat.Prime 536859905969 := by
  apply nodeValid_prime [2, 41, 191, 677, 6329] ⟨536859905969, 3, [(2, 4), (41, 1), (191, 1), (677, 1), (6329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_191
    · exact prime_677
    · exact prime_6329
  · decide +kernel

theorem prime_537715337849 : Nat.Prime 537715337849 := by
  apply nodeValid_prime [2, 13, 229, 22577903] ⟨537715337849, 3, [(2, 3), (13, 1), (229, 1), (22577903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_229
    · exact prime_22577903
  · decide +kernel

theorem prime_537715340077 : Nat.Prime 537715340077 := by
  apply nodeValid_prime [2, 3, 139, 461, 699287] ⟨537715340077, 2, [(2, 2), (3, 1), (139, 1), (461, 1), (699287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_461
    · exact prime_699287
  · decide +kernel

theorem prime_537715340579 : Nat.Prime 537715340579 := by
  apply nodeValid_prime [2, 13, 20681359253] ⟨537715340579, 2, [(2, 1), (13, 1), (20681359253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_20681359253
  · decide +kernel

theorem prime_538571690221 : Nat.Prime 538571690221 := by
  apply nodeValid_prime [2, 3, 5, 17, 528011461] ⟨538571690221, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (528011461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_528011461
  · decide +kernel

theorem prime_538571698421 : Nat.Prime 538571698421 := by
  apply nodeValid_prime [2, 5, 7, 3846940703] ⟨538571698421, 2, [(2, 2), (5, 1), (7, 1), (3846940703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3846940703
  · decide +kernel

theorem prime_538571699291 : Nat.Prime 538571699291 := by
  apply nodeValid_prime [2, 5, 19, 14621, 193871] ⟨538571699291, 2, [(2, 1), (5, 1), (19, 1), (14621, 1), (193871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_14621
    · exact prime_193871
  · decide +kernel

theorem prime_539428971251 : Nat.Prime 539428971251 := by
  apply nodeValid_prime [2, 5, 13, 647, 51307] ⟨539428971251, 6, [(2, 1), (5, 4), (13, 1), (647, 1), (51307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_647
    · exact prime_51307
  · decide +kernel

theorem prime_539428973087 : Nat.Prime 539428973087 := by
  apply nodeValid_prime [2, 148609, 1814927] ⟨539428973087, 5, [(2, 1), (148609, 1), (1814927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_148609
    · exact prime_1814927
  · decide +kernel

theorem prime_539428974113 : Nat.Prime 539428974113 := by
  apply nodeValid_prime [2, 7, 59, 151, 270307] ⟨539428974113, 3, [(2, 5), (7, 1), (59, 1), (151, 1), (270307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_151
    · exact prime_270307
  · decide +kernel

theorem prime_540287105177 : Nat.Prime 540287105177 := by
  apply nodeValid_prime [2, 7, 13, 31, 1327, 18041] ⟨540287105177, 3, [(2, 3), (7, 1), (13, 1), (31, 1), (1327, 1), (18041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_1327
    · exact prime_18041
  · decide +kernel

theorem prime_540287105471 : Nat.Prime 540287105471 := by
  apply nodeValid_prime [2, 5, 7, 431, 773, 23167] ⟨540287105471, 19, [(2, 1), (5, 1), (7, 1), (431, 1), (773, 1), (23167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_431
    · exact prime_773
    · exact prime_23167
  · decide +kernel

theorem prime_540287181457 : Nat.Prime 540287181457 := by
  apply nodeValid_prime [2, 3, 11, 29, 1049, 33637] ⟨540287181457, 5, [(2, 4), (3, 1), (11, 1), (29, 1), (1049, 1), (33637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_1049
    · exact prime_33637
  · decide +kernel

theorem prime_541146283201 : Nat.Prime 541146283201 := by
  apply nodeValid_prime [2, 3, 5, 109, 3163] ⟨541146283201, 11, [(2, 6), (3, 2), (5, 2), (109, 2), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_3163
  · decide +kernel

theorem prime_541146284047 : Nat.Prime 541146284047 := by
  apply nodeValid_prime [2, 3, 739, 40681573] ⟨541146284047, 5, [(2, 1), (3, 2), (739, 1), (40681573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_739
    · exact prime_40681573
  · decide +kernel

theorem prime_541146311581 : Nat.Prime 541146311581 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 241, 281381] ⟨541146311581, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (241, 1), (281381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_241
    · exact prime_281381
  · decide +kernel

theorem prime_542006364709 : Nat.Prime 542006364709 := by
  apply nodeValid_prime [2, 3, 107, 46902593] ⟨542006364709, 6, [(2, 2), (3, 3), (107, 1), (46902593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_46902593
  · decide +kernel

theorem prime_542006374709 : Nat.Prime 542006374709 := by
  apply nodeValid_prime [2, 17, 7970681981] ⟨542006374709, 2, [(2, 2), (17, 1), (7970681981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_7970681981
  · decide +kernel

theorem prime_542006374751 : Nat.Prime 542006374751 := by
  apply nodeValid_prime [2, 5, 101, 3739, 5741] ⟨542006374751, 14, [(2, 1), (5, 3), (101, 1), (3739, 1), (5741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_3739
    · exact prime_5741
  · decide +kernel

theorem prime_542867348563 : Nat.Prime 542867348563 := by
  apply nodeValid_prime [2, 3, 7, 11, 167, 1663, 4231] ⟨542867348563, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (167, 1), (1663, 1), (4231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_167
    · exact prime_1663
    · exact prime_4231
  · decide +kernel

theorem prime_542867357797 : Nat.Prime 542867357797 := by
  apply nodeValid_prime [2, 3, 17, 10399, 15053] ⟨542867357797, 5, [(2, 2), (3, 1), (17, 2), (10399, 1), (15053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_10399
    · exact prime_15053
  · decide +kernel

theorem prime_542867357887 : Nat.Prime 542867357887 := by
  apply nodeValid_prime [2, 3, 7, 2113, 6117091] ⟨542867357887, 5, [(2, 1), (3, 1), (7, 1), (2113, 1), (6117091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2113
    · exact prime_6117091
  · decide +kernel

theorem prime_543729264229 : Nat.Prime 543729264229 := by
  apply nodeValid_prime [2, 3, 281, 397, 135389] ⟨543729264229, 2, [(2, 2), (3, 2), (281, 1), (397, 1), (135389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_397
    · exact prime_135389
  · decide +kernel

theorem prime_543729266471 : Nat.Prime 543729266471 := by
  apply nodeValid_prime [2, 5, 13, 23, 181849253] ⟨543729266471, 17, [(2, 1), (5, 1), (13, 1), (23, 1), (181849253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_181849253
  · decide +kernel

theorem prime_543729267803 : Nat.Prime 543729267803 := by
  apply nodeValid_prime [2, 7, 67, 271, 2138999] ⟨543729267803, 2, [(2, 1), (7, 1), (67, 1), (271, 1), (2138999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_271
    · exact prime_2138999
  · decide +kernel

theorem prime_544592108287 : Nat.Prime 544592108287 := by
  apply nodeValid_prime [2, 3, 137, 220840271] ⟨544592108287, 3, [(2, 1), (3, 2), (137, 1), (220840271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_220840271
  · decide +kernel

theorem prime_544592116741 : Nat.Prime 544592116741 := by
  apply nodeValid_prime [2, 3, 5, 7, 59, 179, 122777] ⟨544592116741, 11, [(2, 2), (3, 1), (5, 1), (7, 1), (59, 1), (179, 1), (122777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_179
    · exact prime_122777
  · decide +kernel

theorem prime_544592117143 : Nat.Prime 544592117143 := by
  apply nodeValid_prime [2, 3, 11299, 2677681] ⟨544592117143, 6, [(2, 1), (3, 2), (11299, 1), (2677681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11299
    · exact prime_2677681
  · decide +kernel

theorem prime_545455890131 : Nat.Prime 545455890131 := by
  apply nodeValid_prime [2, 5, 54545589013] ⟨545455890131, 2, [(2, 1), (5, 1), (54545589013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_54545589013
  · decide +kernel

theorem prime_545455983869 : Nat.Prime 545455983869 := by
  apply nodeValid_prime [2, 271, 503188177] ⟨545455983869, 2, [(2, 2), (271, 1), (503188177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_503188177
  · decide +kernel

theorem prime_545455984259 : Nat.Prime 545455984259 := by
  apply nodeValid_prime [2, 653, 417653893] ⟨545455984259, 2, [(2, 1), (653, 1), (417653893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_653
    · exact prime_417653893
  · decide +kernel

theorem prime_546320580947 : Nat.Prime 546320580947 := by
  apply nodeValid_prime [2, 7, 33713, 1157503] ⟨546320580947, 2, [(2, 1), (7, 1), (33713, 1), (1157503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_33713
    · exact prime_1157503
  · decide +kernel

theorem prime_546320581817 : Nat.Prime 546320581817 := by
  apply nodeValid_prime [2, 617, 110680831] ⟨546320581817, 3, [(2, 3), (617, 1), (110680831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_617
    · exact prime_110680831
  · decide +kernel

theorem prime_546320600851 : Nat.Prime 546320600851 := by
  apply nodeValid_prime [2, 3, 5, 71, 157, 326737] ⟨546320600851, 2, [(2, 1), (3, 1), (5, 2), (71, 1), (157, 1), (326737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_157
    · exact prime_326737
  · decide +kernel

theorem prime_547186239997 : Nat.Prime 547186239997 := by
  apply nodeValid_prime [2, 3, 11, 4145350303] ⟨547186239997, 5, [(2, 2), (3, 1), (11, 1), (4145350303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4145350303
  · decide +kernel

theorem prime_547186258373 : Nat.Prime 547186258373 := by
  apply nodeValid_prime [2, 13, 29, 362855609] ⟨547186258373, 2, [(2, 2), (13, 1), (29, 1), (362855609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_362855609
  · decide +kernel

theorem prime_547186260073 : Nat.Prime 547186260073 := by
  apply nodeValid_prime [2, 3, 23831, 956713] ⟨547186260073, 7, [(2, 3), (3, 1), (23831, 1), (956713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23831
    · exact prime_956713
  · decide +kernel

theorem prime_548052783797 : Nat.Prime 548052783797 := by
  apply nodeValid_prime [2, 7, 19573313707] ⟨548052783797, 2, [(2, 2), (7, 1), (19573313707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19573313707
  · decide +kernel

theorem prime_548052784297 : Nat.Prime 548052784297 := by
  apply nodeValid_prime [2, 3, 19, 1201870141] ⟨548052784297, 11, [(2, 3), (3, 1), (19, 1), (1201870141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1201870141
  · decide +kernel

theorem prime_548052805873 : Nat.Prime 548052805873 := by
  apply nodeValid_prime [2, 3, 11, 13, 23, 59, 1783] ⟨548052805873, 7, [(2, 4), (3, 2), (11, 2), (13, 1), (23, 1), (59, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_59
    · exact prime_1783
  · decide +kernel

theorem prime_548920306373 : Nat.Prime 548920306373 := by
  apply nodeValid_prime [2, 37, 2357, 1573577] ⟨548920306373, 2, [(2, 2), (37, 1), (2357, 1), (1573577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2357
    · exact prime_1573577
  · decide +kernel

theorem prime_548920350731 : Nat.Prime 548920350731 := by
  apply nodeValid_prime [2, 5, 79, 853, 814579] ⟨548920350731, 6, [(2, 1), (5, 1), (79, 1), (853, 1), (814579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_853
    · exact prime_814579
  · decide +kernel

theorem prime_548920354691 : Nat.Prime 548920354691 := by
  apply nodeValid_prime [2, 5, 401, 136887869] ⟨548920354691, 10, [(2, 1), (5, 1), (401, 1), (136887869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_401
    · exact prime_136887869
  · decide +kernel

theorem prime_549788739371 : Nat.Prime 549788739371 := by
  apply nodeValid_prime [2, 5, 13, 14327, 295187] ⟨549788739371, 2, [(2, 1), (5, 1), (13, 1), (14327, 1), (295187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_14327
    · exact prime_295187
  · decide +kernel

theorem prime_549788753599 : Nat.Prime 549788753599 := by
  apply nodeValid_prime [2, 3, 7, 13090208419] ⟨549788753599, 6, [(2, 1), (3, 1), (7, 1), (13090208419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13090208419
  · decide +kernel

theorem prime_549788753687 : Nat.Prime 549788753687 := by
  apply nodeValid_prime [2, 19, 863, 1901, 8819] ⟨549788753687, 10, [(2, 1), (19, 1), (863, 1), (1901, 1), (8819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_863
    · exact prime_1901
    · exact prime_8819
  · decide +kernel

theorem prime_550658101967 : Nat.Prime 550658101967 := by
  apply nodeValid_prime [2, 7, 39332721569] ⟨550658101967, 7, [(2, 1), (7, 1), (39332721569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_39332721569
  · decide +kernel

theorem prime_550658113037 : Nat.Prime 550658113037 := by
  apply nodeValid_prime [2, 17, 8097913427] ⟨550658113037, 2, [(2, 2), (17, 1), (8097913427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_8097913427
  · decide +kernel

theorem prime_550658113039 : Nat.Prime 550658113039 := by
  apply nodeValid_prime [2, 3, 11, 631, 853, 5167] ⟨550658113039, 3, [(2, 1), (3, 2), (11, 1), (631, 1), (853, 1), (5167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_631
    · exact prime_853
    · exact prime_5167
  · decide +kernel

end Sude.Lucas.Generated
