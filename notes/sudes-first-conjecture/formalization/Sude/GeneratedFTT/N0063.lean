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
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3917 : Nat.Prime 3917 := by
  apply nodeValid_prime [2, 11, 89] ⟨3917, 2, [(2, 2), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_5437 : Nat.Prime 5437 := by
  apply nodeValid_prime [2, 3, 151] ⟨5437, 5, [(2, 2), (3, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
  · decide +kernel

theorem prime_10369 : Nat.Prime 10369 := by
  apply nodeValid_prime [2, 3] ⟨10369, 13, [(2, 7), (3, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_14891 : Nat.Prime 14891 := by
  apply nodeValid_prime [2, 5, 1489] ⟨14891, 2, [(2, 1), (5, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1489
  · decide +kernel

theorem prime_20599 : Nat.Prime 20599 := by
  apply nodeValid_prime [2, 3, 3433] ⟨20599, 3, [(2, 1), (3, 1), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3433
  · decide +kernel

theorem prime_23531 : Nat.Prime 23531 := by
  apply nodeValid_prime [2, 5, 13, 181] ⟨23531, 2, [(2, 1), (5, 1), (13, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_181
  · decide +kernel

theorem prime_24049 : Nat.Prime 24049 := by
  apply nodeValid_prime [2, 3, 167] ⟨24049, 19, [(2, 4), (3, 2), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
  · decide +kernel

theorem prime_24239 : Nat.Prime 24239 := by
  apply nodeValid_prime [2, 12119] ⟨24239, 13, [(2, 1), (12119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12119
  · decide +kernel

theorem prime_25759 : Nat.Prime 25759 := by
  apply nodeValid_prime [2, 3, 53] ⟨25759, 3, [(2, 1), (3, 5), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
  · decide +kernel

theorem prime_28439 : Nat.Prime 28439 := by
  apply nodeValid_prime [2, 59, 241] ⟨28439, 11, [(2, 1), (59, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_241
  · decide +kernel

theorem prime_29947 : Nat.Prime 29947 := by
  apply nodeValid_prime [2, 3, 7, 23, 31] ⟨29947, 3, [(2, 1), (3, 1), (7, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_32143 : Nat.Prime 32143 := by
  apply nodeValid_prime [2, 3, 11, 487] ⟨32143, 6, [(2, 1), (3, 1), (11, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_487
  · decide +kernel

theorem prime_32413 : Nat.Prime 32413 := by
  apply nodeValid_prime [2, 3, 37, 73] ⟨32413, 5, [(2, 2), (3, 1), (37, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_73
  · decide +kernel

theorem prime_40927 : Nat.Prime 40927 := by
  apply nodeValid_prime [2, 3, 19, 359] ⟨40927, 3, [(2, 1), (3, 1), (19, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_359
  · decide +kernel

theorem prime_42323 : Nat.Prime 42323 := by
  apply nodeValid_prime [2, 7, 3023] ⟨42323, 2, [(2, 1), (7, 1), (3023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3023
  · decide +kernel

theorem prime_44159 : Nat.Prime 44159 := by
  apply nodeValid_prime [2, 22079] ⟨44159, 11, [(2, 1), (22079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22079
  · decide +kernel

theorem prime_45119 : Nat.Prime 45119 := by
  apply nodeValid_prime [2, 17, 1327] ⟨45119, 7, [(2, 1), (17, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1327
  · decide +kernel

theorem prime_46093 : Nat.Prime 46093 := by
  apply nodeValid_prime [2, 3, 23, 167] ⟨46093, 2, [(2, 2), (3, 1), (23, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_167
  · decide +kernel

theorem prime_48479 : Nat.Prime 48479 := by
  apply nodeValid_prime [2, 24239] ⟨48479, 7, [(2, 1), (24239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24239
  · decide +kernel

theorem prime_67391 : Nat.Prime 67391 := by
  apply nodeValid_prime [2, 5, 23, 293] ⟨67391, 7, [(2, 1), (5, 1), (23, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_293
  · decide +kernel

theorem prime_77477 : Nat.Prime 77477 := by
  apply nodeValid_prime [2, 7, 2767] ⟨77477, 2, [(2, 2), (7, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2767
  · decide +kernel

theorem prime_86857 : Nat.Prime 86857 := by
  apply nodeValid_prime [2, 3, 7, 11, 47] ⟨86857, 10, [(2, 3), (3, 1), (7, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_90239 : Nat.Prime 90239 := by
  apply nodeValid_prime [2, 45119] ⟨90239, 7, [(2, 1), (45119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45119
  · decide +kernel

theorem prime_96013 : Nat.Prime 96013 := by
  apply nodeValid_prime [2, 3, 7, 127] ⟨96013, 2, [(2, 2), (3, 3), (7, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127
  · decide +kernel

theorem prime_107599 : Nat.Prime 107599 := by
  apply nodeValid_prime [2, 3, 79, 227] ⟨107599, 3, [(2, 1), (3, 1), (79, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_227
  · decide +kernel

theorem prime_117511 : Nat.Prime 117511 := by
  apply nodeValid_prime [2, 3, 5, 3917] ⟨117511, 6, [(2, 1), (3, 1), (5, 1), (3917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3917
  · decide +kernel

theorem prime_127913 : Nat.Prime 127913 := by
  apply nodeValid_prime [2, 59, 271] ⟨127913, 3, [(2, 3), (59, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_271
  · decide +kernel

theorem prime_128393 : Nat.Prime 128393 := by
  apply nodeValid_prime [2, 11, 1459] ⟨128393, 3, [(2, 3), (11, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1459
  · decide +kernel

theorem prime_129023 : Nat.Prime 129023 := by
  apply nodeValid_prime [2, 31, 2081] ⟨129023, 5, [(2, 1), (31, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2081
  · decide +kernel

theorem prime_135431 : Nat.Prime 135431 := by
  apply nodeValid_prime [2, 5, 29, 467] ⟨135431, 7, [(2, 1), (5, 1), (29, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_467
  · decide +kernel

theorem prime_149441 : Nat.Prime 149441 := by
  apply nodeValid_prime [2, 5, 467] ⟨149441, 3, [(2, 6), (5, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_467
  · decide +kernel

theorem prime_170029 : Nat.Prime 170029 := by
  apply nodeValid_prime [2, 3, 4723] ⟨170029, 2, [(2, 2), (3, 2), (4723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4723
  · decide +kernel

theorem prime_194479 : Nat.Prime 194479 := by
  apply nodeValid_prime [2, 3, 32413] ⟨194479, 3, [(2, 1), (3, 1), (32413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32413
  · decide +kernel

theorem prime_211597 : Nat.Prime 211597 := by
  apply nodeValid_prime [2, 3, 7, 11, 229] ⟨211597, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_229
  · decide +kernel

theorem prime_245563 : Nat.Prime 245563 := by
  apply nodeValid_prime [2, 3, 40927] ⟨245563, 2, [(2, 1), (3, 1), (40927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40927
  · decide +kernel

theorem prime_324113 : Nat.Prime 324113 := by
  apply nodeValid_prime [2, 47, 431] ⟨324113, 3, [(2, 4), (47, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_431
  · decide +kernel

theorem prime_334699 : Nat.Prime 334699 := by
  apply nodeValid_prime [2, 3, 7, 13, 613] ⟨334699, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_613
  · decide +kernel

theorem prime_348833 : Nat.Prime 348833 := by
  apply nodeValid_prime [2, 11, 991] ⟨348833, 3, [(2, 5), (11, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_991
  · decide +kernel

theorem prime_393073 : Nat.Prime 393073 := by
  apply nodeValid_prime [2, 3, 19, 431] ⟨393073, 10, [(2, 4), (3, 1), (19, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_431
  · decide +kernel

theorem prime_424709 : Nat.Prime 424709 := by
  apply nodeValid_prime [2, 89, 1193] ⟨424709, 2, [(2, 2), (89, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1193
  · decide +kernel

theorem prime_461053 : Nat.Prime 461053 := by
  apply nodeValid_prime [2, 3, 1423] ⟨461053, 2, [(2, 2), (3, 4), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1423
  · decide +kernel

theorem prime_479797 : Nat.Prime 479797 := by
  apply nodeValid_prime [2, 3, 39983] ⟨479797, 2, [(2, 2), (3, 1), (39983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39983
  · decide +kernel

theorem prime_489329 : Nat.Prime 489329 := by
  apply nodeValid_prime [2, 7, 17, 257] ⟨489329, 3, [(2, 4), (7, 1), (17, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_257
  · decide +kernel

theorem prime_577627 : Nat.Prime 577627 := by
  apply nodeValid_prime [2, 3, 7, 17, 809] ⟨577627, 12, [(2, 1), (3, 1), (7, 1), (17, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_809
  · decide +kernel

theorem prime_584897 : Nat.Prime 584897 := by
  apply nodeValid_prime [2, 13, 19, 37] ⟨584897, 3, [(2, 6), (13, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_605393 : Nat.Prime 605393 := by
  apply nodeValid_prime [2, 157, 241] ⟨605393, 3, [(2, 4), (157, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_241
  · decide +kernel

theorem prime_639157 : Nat.Prime 639157 := by
  apply nodeValid_prime [2, 3, 7, 1087] ⟨639157, 2, [(2, 2), (3, 1), (7, 2), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1087
  · decide +kernel

theorem prime_728681 : Nat.Prime 728681 := by
  apply nodeValid_prime [2, 5, 18217] ⟨728681, 3, [(2, 3), (5, 1), (18217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18217
  · decide +kernel

theorem prime_807241 : Nat.Prime 807241 := by
  apply nodeValid_prime [2, 3, 5, 7, 31] ⟨807241, 26, [(2, 3), (3, 1), (5, 1), (7, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_872623 : Nat.Prime 872623 := by
  apply nodeValid_prime [2, 3, 48479] ⟨872623, 6, [(2, 1), (3, 2), (48479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48479
  · decide +kernel

theorem prime_878573 : Nat.Prime 878573 := by
  apply nodeValid_prime [2, 157, 1399] ⟨878573, 2, [(2, 2), (157, 1), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_1399
  · decide +kernel

theorem prime_896647 : Nat.Prime 896647 := by
  apply nodeValid_prime [2, 3, 149441] ⟨896647, 3, [(2, 1), (3, 1), (149441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149441
  · decide +kernel

theorem prime_960131 : Nat.Prime 960131 := by
  apply nodeValid_prime [2, 5, 96013] ⟨960131, 2, [(2, 1), (5, 1), (96013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_96013
  · decide +kernel

theorem prime_1026709 : Nat.Prime 1026709 := by
  apply nodeValid_prime [2, 3, 67, 1277] ⟨1026709, 2, [(2, 2), (3, 1), (67, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1277
  · decide +kernel

theorem prime_1080683 : Nat.Prime 1080683 := by
  apply nodeValid_prime [2, 19, 28439] ⟨1080683, 2, [(2, 1), (19, 1), (28439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_28439
  · decide +kernel

theorem prime_1197199 : Nat.Prime 1197199 := by
  apply nodeValid_prime [2, 3, 227, 293] ⟨1197199, 3, [(2, 1), (3, 2), (227, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_293
  · decide +kernel

theorem prime_1893733 : Nat.Prime 1893733 := by
  apply nodeValid_prime [2, 3, 17, 9283] ⟨1893733, 2, [(2, 2), (3, 1), (17, 1), (9283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9283
  · decide +kernel

theorem prime_2310509 : Nat.Prime 2310509 := by
  apply nodeValid_prime [2, 577627] ⟨2310509, 2, [(2, 2), (577627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_577627
  · decide +kernel

theorem prime_3516103 : Nat.Prime 3516103 := by
  apply nodeValid_prime [2, 3, 19, 23, 149] ⟨3516103, 3, [(2, 1), (3, 3), (19, 1), (23, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_149
  · decide +kernel

theorem prime_3942397 : Nat.Prime 3942397 := by
  apply nodeValid_prime [2, 3, 41, 2671] ⟨3942397, 2, [(2, 2), (3, 2), (41, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2671
  · decide +kernel

theorem prime_4797971 : Nat.Prime 4797971 := by
  apply nodeValid_prime [2, 5, 479797] ⟨4797971, 2, [(2, 1), (5, 1), (479797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479797
  · decide +kernel

theorem prime_5327897 : Nat.Prime 5327897 := by
  apply nodeValid_prime [2, 7, 89, 1069] ⟨5327897, 3, [(2, 3), (7, 1), (89, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_1069
  · decide +kernel

theorem prime_5746567 : Nat.Prime 5746567 := by
  apply nodeValid_prime [2, 3, 7, 61, 2243] ⟨5746567, 6, [(2, 1), (3, 1), (7, 1), (61, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_2243
  · decide +kernel

theorem prime_8324039 : Nat.Prime 8324039 := by
  apply nodeValid_prime [2, 37, 197, 571] ⟨8324039, 11, [(2, 1), (37, 1), (197, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_197
    · exact prime_571
  · decide +kernel

theorem prime_8720837 : Nat.Prime 8720837 := by
  apply nodeValid_prime [2, 127, 17167] ⟨8720837, 2, [(2, 2), (127, 1), (17167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_17167
  · decide +kernel

theorem prime_10770269 : Nat.Prime 10770269 := by
  apply nodeValid_prime [2, 31, 86857] ⟨10770269, 2, [(2, 2), (31, 1), (86857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_86857
  · decide +kernel

theorem prime_12314173 : Nat.Prime 12314173 := by
  apply nodeValid_prime [2, 3, 13, 193, 409] ⟨12314173, 14, [(2, 2), (3, 1), (13, 1), (193, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_193
    · exact prime_409
  · decide +kernel

theorem prime_14542159 : Nat.Prime 14542159 := by
  apply nodeValid_prime [2, 3, 103, 23531] ⟨14542159, 7, [(2, 1), (3, 1), (103, 1), (23531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_23531
  · decide +kernel

theorem prime_14698699 : Nat.Prime 14698699 := by
  apply nodeValid_prime [2, 3, 7, 269, 1301] ⟨14698699, 10, [(2, 1), (3, 1), (7, 1), (269, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_269
    · exact prime_1301
  · decide +kernel

theorem prime_15731201 : Nat.Prime 15731201 := by
  apply nodeValid_prime [2, 5, 1229] ⟨15731201, 3, [(2, 9), (5, 2), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1229
  · decide +kernel

theorem prime_18484073 : Nat.Prime 18484073 := by
  apply nodeValid_prime [2, 2310509] ⟨18484073, 3, [(2, 3), (2310509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2310509
  · decide +kernel

theorem prime_18806497 : Nat.Prime 18806497 := by
  apply nodeValid_prime [2, 3, 227, 863] ⟨18806497, 5, [(2, 5), (3, 1), (227, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_863
  · decide +kernel

theorem prime_19475461 : Nat.Prime 19475461 := by
  apply nodeValid_prime [2, 3, 5, 257, 421] ⟨19475461, 2, [(2, 2), (3, 2), (5, 1), (257, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
    · exact prime_421
  · decide +kernel

theorem prime_33549563 : Nat.Prime 33549563 := by
  apply nodeValid_prime [2, 41, 79, 5179] ⟨33549563, 2, [(2, 1), (41, 1), (79, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_79
    · exact prime_5179
  · decide +kernel

theorem prime_42944201 : Nat.Prime 42944201 := by
  apply nodeValid_prime [2, 5, 13, 83, 199] ⟨42944201, 6, [(2, 3), (5, 2), (13, 1), (83, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_83
    · exact prime_199
  · decide +kernel

theorem prime_51978709 : Nat.Prime 51978709 := by
  apply nodeValid_prime [2, 3, 1093, 1321] ⟨51978709, 6, [(2, 2), (3, 2), (1093, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1093
    · exact prime_1321
  · decide +kernel

theorem prime_66405797 : Nat.Prime 66405797 := by
  apply nodeValid_prime [2, 3539, 4691] ⟨66405797, 2, [(2, 2), (3539, 1), (4691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3539
    · exact prime_4691
  · decide +kernel

theorem prime_70006033 : Nat.Prime 70006033 := by
  apply nodeValid_prime [2, 3, 19, 2843] ⟨70006033, 7, [(2, 4), (3, 4), (19, 1), (2843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2843
  · decide +kernel

theorem prime_82031827 : Nat.Prime 82031827 := by
  apply nodeValid_prime [2, 3, 47, 191, 1523] ⟨82031827, 2, [(2, 1), (3, 1), (47, 1), (191, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_191
    · exact prime_1523
  · decide +kernel

theorem prime_94624979 : Nat.Prime 94624979 := by
  apply nodeValid_prime [2, 7, 19, 89, 571] ⟨94624979, 6, [(2, 1), (7, 2), (19, 1), (89, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_89
    · exact prime_571
  · decide +kernel

theorem prime_103819181 : Nat.Prime 103819181 := by
  apply nodeValid_prime [2, 5, 67, 77477] ⟨103819181, 2, [(2, 2), (5, 1), (67, 1), (77477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_77477
  · decide +kernel

theorem prime_119547503 : Nat.Prime 119547503 := by
  apply nodeValid_prime [2, 17, 3516103] ⟨119547503, 5, [(2, 1), (17, 1), (3516103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3516103
  · decide +kernel

theorem prime_125501749 : Nat.Prime 125501749 := by
  apply nodeValid_prime [2, 3, 89, 117511] ⟨125501749, 2, [(2, 2), (3, 1), (89, 1), (117511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_117511
  · decide +kernel

theorem prime_131602447 : Nat.Prime 131602447 := by
  apply nodeValid_prime [2, 3, 43, 170029] ⟨131602447, 6, [(2, 1), (3, 2), (43, 1), (170029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_170029
  · decide +kernel

theorem prime_151700699 : Nat.Prime 151700699 := by
  apply nodeValid_prime [2, 79, 960131] ⟨151700699, 2, [(2, 1), (79, 1), (960131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_960131
  · decide +kernel

theorem prime_185321683 : Nat.Prime 185321683 := by
  apply nodeValid_prime [2, 3, 7, 13, 967] ⟨185321683, 2, [(2, 1), (3, 4), (7, 1), (13, 2), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_967
  · decide +kernel

theorem prime_192702143 : Nat.Prime 192702143 := by
  apply nodeValid_prime [2, 19, 23, 37, 59, 101] ⟨192702143, 5, [(2, 1), (19, 1), (23, 1), (37, 1), (59, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_37
    · exact prime_59
    · exact prime_101
  · decide +kernel

theorem prime_263208931 : Nat.Prime 263208931 := by
  apply nodeValid_prime [2, 3, 5, 29, 41, 47, 157] ⟨263208931, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (41, 1), (47, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_41
    · exact prime_47
    · exact prime_157
  · decide +kernel

theorem prime_265747571 : Nat.Prime 265747571 := by
  apply nodeValid_prime [2, 5, 11, 17, 142111] ⟨265747571, 2, [(2, 1), (5, 1), (11, 1), (17, 1), (142111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_142111
  · decide +kernel

theorem prime_265953239 : Nat.Prime 265953239 := by
  apply nodeValid_prime [2, 59, 2253841] ⟨265953239, 13, [(2, 1), (59, 1), (2253841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2253841
  · decide +kernel

theorem prime_278947727 : Nat.Prime 278947727 := by
  apply nodeValid_prime [2, 23, 47, 129023] ⟨278947727, 5, [(2, 1), (23, 1), (47, 1), (129023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_129023
  · decide +kernel

theorem prime_328127309 : Nat.Prime 328127309 := by
  apply nodeValid_prime [2, 82031827] ⟨328127309, 2, [(2, 2), (82031827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82031827
  · decide +kernel

theorem prime_706569371 : Nat.Prime 706569371 := by
  apply nodeValid_prime [2, 5, 13, 211, 25759] ⟨706569371, 2, [(2, 1), (5, 1), (13, 1), (211, 1), (25759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_211
    · exact prime_25759
  · decide +kernel

theorem prime_776331067 : Nat.Prime 776331067 := by
  apply nodeValid_prime [2, 3, 7, 18484073] ⟨776331067, 2, [(2, 1), (3, 1), (7, 1), (18484073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18484073
  · decide +kernel

theorem prime_784875331 : Nat.Prime 784875331 := by
  apply nodeValid_prime [2, 3, 5, 8720837] ⟨784875331, 3, [(2, 1), (3, 2), (5, 1), (8720837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8720837
  · decide +kernel

theorem prime_1061554913 : Nat.Prime 1061554913 := by
  apply nodeValid_prime [2, 11, 137, 22013] ⟨1061554913, 3, [(2, 5), (11, 1), (137, 1), (22013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_137
    · exact prime_22013
  · decide +kernel

theorem prime_1230394939 : Nat.Prime 1230394939 := by
  apply nodeValid_prime [2, 3, 8527, 24049] ⟨1230394939, 2, [(2, 1), (3, 1), (8527, 1), (24049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8527
    · exact prime_24049
  · decide +kernel

theorem prime_1917173983 : Nat.Prime 1917173983 := by
  apply nodeValid_prime [2, 3, 31, 53, 194479] ⟨1917173983, 3, [(2, 1), (3, 1), (31, 1), (53, 1), (194479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
    · exact prime_194479
  · decide +kernel

theorem prime_2173133801 : Nat.Prime 2173133801 := by
  apply nodeValid_prime [2, 5, 17, 639157] ⟨2173133801, 3, [(2, 3), (5, 2), (17, 1), (639157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_639157
  · decide +kernel

theorem prime_3098147189 : Nat.Prime 3098147189 := by
  apply nodeValid_prime [2, 409, 1893733] ⟨3098147189, 2, [(2, 2), (409, 1), (1893733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_1893733
  · decide +kernel

theorem prime_3105324269 : Nat.Prime 3105324269 := by
  apply nodeValid_prime [2, 776331067] ⟨3105324269, 2, [(2, 2), (776331067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_776331067
  · decide +kernel

theorem prime_3945128879 : Nat.Prime 3945128879 := by
  apply nodeValid_prime [2, 19, 103819181] ⟨3945128879, 17, [(2, 1), (19, 1), (103819181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_103819181
  · decide +kernel

theorem prime_5042602189 : Nat.Prime 5042602189 := by
  apply nodeValid_prime [2, 3, 13, 1197199] ⟨5042602189, 2, [(2, 2), (3, 4), (13, 1), (1197199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1197199
  · decide +kernel

theorem prime_5837623963 : Nat.Prime 5837623963 := by
  apply nodeValid_prime [2, 3, 29, 33549563] ⟨5837623963, 3, [(2, 1), (3, 1), (29, 1), (33549563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_33549563
  · decide +kernel

theorem prime_9079941029 : Nat.Prime 9079941029 := by
  apply nodeValid_prime [2, 3881, 584897] ⟨9079941029, 2, [(2, 2), (3881, 1), (584897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3881
    · exact prime_584897
  · decide +kernel

theorem prime_16626958643 : Nat.Prime 16626958643 := by
  apply nodeValid_prime [2, 7, 1361, 872623] ⟨16626958643, 2, [(2, 1), (7, 1), (1361, 1), (872623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1361
    · exact prime_872623
  · decide +kernel

theorem prime_18138194567 : Nat.Prime 18138194567 := by
  apply nodeValid_prime [2, 617, 14698699] ⟨18138194567, 5, [(2, 1), (617, 1), (14698699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_617
    · exact prime_14698699
  · decide +kernel

theorem prime_20782799707 : Nat.Prime 20782799707 := by
  apply nodeValid_prime [2, 3, 79, 131, 334699] ⟨20782799707, 2, [(2, 1), (3, 1), (79, 1), (131, 1), (334699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_131
    · exact prime_334699
  · decide +kernel

theorem prime_101909271649 : Nat.Prime 101909271649 := by
  apply nodeValid_prime [2, 3, 1061554913] ⟨101909271649, 7, [(2, 5), (3, 1), (1061554913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1061554913
  · decide +kernel

theorem prime_103284675913 : Nat.Prime 103284675913 := by
  apply nodeValid_prime [2, 3, 11, 47, 8324039] ⟨103284675913, 10, [(2, 3), (3, 1), (11, 1), (47, 1), (8324039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_8324039
  · decide +kernel

theorem prime_204566291557 : Nat.Prime 204566291557 := by
  apply nodeValid_prime [2, 3, 11, 17, 19, 4797971] ⟨204566291557, 2, [(2, 2), (3, 1), (11, 1), (17, 1), (19, 1), (4797971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_4797971
  · decide +kernel

theorem prime_207827997071 : Nat.Prime 207827997071 := by
  apply nodeValid_prime [2, 5, 20782799707] ⟨207827997071, 7, [(2, 1), (5, 1), (20782799707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20782799707
  · decide +kernel

theorem prime_306475257883 : Nat.Prime 306475257883 := by
  apply nodeValid_prime [2, 3, 17, 191, 15731201] ⟨306475257883, 2, [(2, 1), (3, 1), (17, 1), (191, 1), (15731201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_191
    · exact prime_15731201
  · decide +kernel

theorem prime_621971744609 : Nat.Prime 621971744609 := by
  apply nodeValid_prime [2, 53, 409, 896647] ⟨621971744609, 3, [(2, 5), (53, 1), (409, 1), (896647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_409
    · exact prime_896647
  · decide +kernel

theorem prime_1222911259789 : Nat.Prime 1222911259789 := by
  apply nodeValid_prime [2, 3, 101909271649] ⟨1222911259789, 2, [(2, 2), (3, 1), (101909271649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101909271649
  · decide +kernel

theorem prime_1222911273923 : Nat.Prime 1222911273923 := by
  apply nodeValid_prime [2, 13, 41, 61, 18806497] ⟨1222911273923, 2, [(2, 1), (13, 1), (41, 1), (61, 1), (18806497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_61
    · exact prime_18806497
  · decide +kernel

theorem prime_1222911274469 : Nat.Prime 1222911274469 := by
  apply nodeValid_prime [2, 13, 29, 197, 397, 10369] ⟨1222911274469, 2, [(2, 2), (13, 1), (29, 1), (197, 1), (397, 1), (10369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_197
    · exact prime_397
    · exact prime_10369
  · decide +kernel

theorem prime_1224405516361 : Nat.Prime 1224405516361 := by
  apply nodeValid_prime [2, 3, 5, 13, 784875331] ⟨1224405516361, 7, [(2, 3), (3, 1), (5, 1), (13, 1), (784875331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_784875331
  · decide +kernel

theorem prime_1224405517171 : Nat.Prime 1224405517171 := by
  apply nodeValid_prime [2, 3, 5, 11, 53, 70006033] ⟨1224405517171, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (70006033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_53
    · exact prime_70006033
  · decide +kernel

theorem prime_1224405525727 : Nat.Prime 1224405525727 := by
  apply nodeValid_prime [2, 3, 569, 119547503] ⟨1224405525727, 3, [(2, 1), (3, 2), (569, 1), (119547503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
    · exact prime_119547503
  · decide +kernel

theorem prime_1225901021237 : Nat.Prime 1225901021237 := by
  apply nodeValid_prime [2, 348833, 878573] ⟨1225901021237, 2, [(2, 2), (348833, 1), (878573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_348833
    · exact prime_878573
  · decide +kernel

theorem prime_1225901031533 : Nat.Prime 1225901031533 := by
  apply nodeValid_prime [2, 306475257883] ⟨1225901031533, 2, [(2, 2), (306475257883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_306475257883
  · decide +kernel

theorem prime_1225901032231 : Nat.Prime 1225901032231 := by
  apply nodeValid_prime [2, 3, 5, 7, 5837623963] ⟨1225901032231, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (5837623963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_5837623963
  · decide +kernel

theorem prime_1227397749343 : Nat.Prime 1227397749343 := by
  apply nodeValid_prime [2, 3, 204566291557] ⟨1227397749343, 3, [(2, 1), (3, 1), (204566291557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_204566291557
  · decide +kernel

theorem prime_1227397752397 : Nat.Prime 1227397752397 := by
  apply nodeValid_prime [2, 3, 17, 349, 5746567] ⟨1227397752397, 2, [(2, 2), (3, 2), (17, 1), (349, 1), (5746567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_349
    · exact prime_5746567
  · decide +kernel

theorem prime_1227397754813 : Nat.Prime 1227397754813 := by
  apply nodeValid_prime [2, 53, 5639, 1026709] ⟨1227397754813, 2, [(2, 2), (53, 1), (5639, 1), (1026709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_5639
    · exact prime_1026709
  · decide +kernel

theorem prime_1228895705647 : Nat.Prime 1228895705647 := by
  apply nodeValid_prime [2, 3, 7, 46093, 211597] ⟨1228895705647, 5, [(2, 1), (3, 2), (7, 1), (46093, 1), (211597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_46093
    · exact prime_211597
  · decide +kernel

theorem prime_1228895706761 : Nat.Prime 1228895706761 := by
  apply nodeValid_prime [2, 5, 23, 37, 853, 42323] ⟨1228895706761, 3, [(2, 3), (5, 1), (23, 1), (37, 1), (853, 1), (42323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_853
    · exact prime_42323
  · decide +kernel

theorem prime_1228895726203 : Nat.Prime 1228895726203 := by
  apply nodeValid_prime [2, 3, 37591, 605393] ⟨1228895726203, 2, [(2, 1), (3, 3), (37591, 1), (605393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37591
    · exact prime_605393
  · decide +kernel

theorem prime_1230394934117 : Nat.Prime 1230394934117 := by
  apply nodeValid_prime [2, 61, 5042602189] ⟨1230394934117, 2, [(2, 2), (61, 1), (5042602189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_5042602189
  · decide +kernel

theorem prime_1230394939001 : Nat.Prime 1230394939001 := by
  apply nodeValid_prime [2, 5, 1230394939] ⟨1230394939001, 3, [(2, 3), (5, 3), (1230394939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1230394939
  · decide +kernel

theorem prime_1230394939583 : Nat.Prime 1230394939583 := by
  apply nodeValid_prime [2, 37, 16626958643] ⟨1230394939583, 5, [(2, 1), (37, 1), (16626958643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_16626958643
  · decide +kernel

theorem prime_1231895373209 : Nat.Prime 1231895373209 := by
  apply nodeValid_prime [2, 10589, 14542159] ⟨1231895373209, 3, [(2, 3), (10589, 1), (14542159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10589
    · exact prime_14542159
  · decide +kernel

theorem prime_1231895403049 : Nat.Prime 1231895403049 := by
  apply nodeValid_prime [2, 3, 193, 265953239] ⟨1231895403049, 7, [(2, 3), (3, 1), (193, 1), (265953239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_265953239
  · decide +kernel

theorem prime_1231895403301 : Nat.Prime 1231895403301 := by
  apply nodeValid_prime [2, 3, 5, 79, 51978709] ⟨1231895403301, 2, [(2, 2), (3, 1), (5, 2), (79, 1), (51978709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_51978709
  · decide +kernel

theorem prime_1233397050667 : Nat.Prime 1233397050667 := by
  apply nodeValid_prime [2, 3, 11, 71, 263208931] ⟨1233397050667, 2, [(2, 1), (3, 1), (11, 1), (71, 1), (263208931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_71
    · exact prime_263208931
  · decide +kernel

theorem prime_1233397230557 : Nat.Prime 1233397230557 := by
  apply nodeValid_prime [2, 17, 18138194567] ⟨1233397230557, 2, [(2, 2), (17, 1), (18138194567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_18138194567
  · decide +kernel

theorem prime_1233397231727 : Nat.Prime 1233397231727 := by
  apply nodeValid_prime [2, 11, 1229, 6101, 7477] ⟨1233397231727, 5, [(2, 1), (11, 1), (1229, 1), (6101, 1), (7477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1229
    · exact prime_6101
    · exact prime_7477
  · decide +kernel

theorem prime_1234899966661 : Nat.Prime 1234899966661 := by
  apply nodeValid_prime [2, 3, 5, 3863, 5327897] ⟨1234899966661, 2, [(2, 2), (3, 1), (5, 1), (3863, 1), (5327897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3863
    · exact prime_5327897
  · decide +kernel

theorem prime_1234900031003 : Nat.Prime 1234900031003 := by
  apply nodeValid_prime [2, 11, 211, 577, 461053] ⟨1234900031003, 2, [(2, 1), (11, 1), (211, 1), (577, 1), (461053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_211
    · exact prime_577
    · exact prime_461053
  · decide +kernel

theorem prime_1234900031089 : Nat.Prime 1234900031089 := by
  apply nodeValid_prime [2, 3, 1321, 19475461] ⟨1234900031089, 22, [(2, 4), (3, 1), (1321, 1), (19475461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1321
    · exact prime_19475461
  · decide +kernel

theorem prime_1236404122157 : Nat.Prime 1236404122157 := by
  apply nodeValid_prime [2, 7, 67, 109, 727, 8317] ⟨1236404122157, 2, [(2, 2), (7, 1), (67, 1), (109, 1), (727, 1), (8317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_109
    · exact prime_727
    · exact prime_8317
  · decide +kernel

theorem prime_1236404219723 : Nat.Prime 1236404219723 := by
  apply nodeValid_prime [2, 7, 15629, 807241] ⟨1236404219723, 2, [(2, 1), (7, 2), (15629, 1), (807241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15629
    · exact prime_807241
  · decide +kernel

theorem prime_1236404221487 : Nat.Prime 1236404221487 := by
  apply nodeValid_prime [2, 7, 19, 23, 59, 489329] ⟨1236404221487, 5, [(2, 1), (7, 2), (19, 1), (23, 1), (59, 1), (489329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_59
    · exact prime_489329
  · decide +kernel

theorem prime_1237909515317 : Nat.Prime 1237909515317 := by
  apply nodeValid_prime [2, 424709, 728681] ⟨1237909515317, 2, [(2, 2), (424709, 1), (728681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_424709
    · exact prime_728681
  · decide +kernel

theorem prime_1237909537993 : Nat.Prime 1237909537993 := by
  apply nodeValid_prime [2, 3, 73, 706569371] ⟨1237909537993, 10, [(2, 3), (3, 1), (73, 1), (706569371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_706569371
  · decide +kernel

theorem prime_1237909538027 : Nat.Prime 1237909538027 := by
  apply nodeValid_prime [2, 7, 29, 71, 42944201] ⟨1237909538027, 2, [(2, 1), (7, 1), (29, 1), (71, 1), (42944201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_71
    · exact prime_42944201
  · decide +kernel

theorem prime_1239416108771 : Nat.Prime 1239416108771 := by
  apply nodeValid_prime [2, 5, 7, 131, 5441, 24841] ⟨1239416108771, 2, [(2, 1), (5, 1), (7, 1), (131, 1), (5441, 1), (24841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_131
    · exact prime_5441
    · exact prime_24841
  · decide +kernel

theorem prime_1239416110957 : Nat.Prime 1239416110957 := by
  apply nodeValid_prime [2, 3, 103284675913] ⟨1239416110957, 2, [(2, 2), (3, 1), (103284675913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103284675913
  · decide +kernel

theorem prime_1239416146901 : Nat.Prime 1239416146901 := by
  apply nodeValid_prime [2, 5, 37, 2609, 128393] ⟨1239416146901, 2, [(2, 2), (5, 2), (37, 1), (2609, 1), (128393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_2609
    · exact prime_128393
  · decide +kernel

theorem prime_1240924026763 : Nat.Prime 1240924026763 := by
  apply nodeValid_prime [2, 3, 7, 17, 2341, 35353] ⟨1240924026763, 5, [(2, 1), (3, 2), (7, 2), (17, 1), (2341, 1), (35353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_2341
    · exact prime_35353
  · decide +kernel

theorem prime_1240924134041 : Nat.Prime 1240924134041 := by
  apply nodeValid_prime [2, 5, 277, 5437, 20599] ⟨1240924134041, 3, [(2, 3), (5, 1), (277, 1), (5437, 1), (20599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_277
    · exact prime_5437
    · exact prime_20599
  · decide +kernel

theorem prime_1240924135193 : Nat.Prime 1240924135193 := by
  apply nodeValid_prime [2, 7, 90239, 245563] ⟨1240924135193, 3, [(2, 3), (7, 1), (90239, 1), (245563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_90239
    · exact prime_245563
  · decide +kernel

theorem prime_1242433147343 : Nat.Prime 1242433147343 := by
  apply nodeValid_prime [2, 59, 9743, 1080683] ⟨1242433147343, 5, [(2, 1), (59, 1), (9743, 1), (1080683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_9743
    · exact prime_1080683
  · decide +kernel

theorem prime_1242433171517 : Nat.Prime 1242433171517 := by
  apply nodeValid_prime [2, 307, 9403, 107599] ⟨1242433171517, 2, [(2, 2), (307, 1), (9403, 1), (107599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_9403
    · exact prime_107599
  · decide +kernel

theorem prime_1242433176059 : Nat.Prime 1242433176059 := by
  apply nodeValid_prime [2, 17, 131, 278947727] ⟨1242433176059, 2, [(2, 1), (17, 1), (131, 1), (278947727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_131
    · exact prime_278947727
  · decide +kernel

theorem prime_1243943486033 : Nat.Prime 1243943486033 := by
  apply nodeValid_prime [2, 13, 44159, 135431] ⟨1243943486033, 3, [(2, 4), (13, 1), (44159, 1), (135431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_44159
    · exact prime_135431
  · decide +kernel

theorem prime_1243943489219 : Nat.Prime 1243943489219 := by
  apply nodeValid_prime [2, 621971744609] ⟨1243943489219, 2, [(2, 1), (621971744609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_621971744609
  · decide +kernel

theorem prime_1243943512193 : Nat.Prime 1243943512193 := by
  apply nodeValid_prime [2, 17, 19, 4093, 7351] ⟨1243943512193, 5, [(2, 7), (17, 1), (19, 1), (4093, 1), (7351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_4093
    · exact prime_7351
  · decide +kernel

theorem prime_1245455125793 : Nat.Prime 1245455125793 := by
  apply nodeValid_prime [2, 389, 6719, 14891] ⟨1245455125793, 3, [(2, 5), (389, 1), (6719, 1), (14891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_389
    · exact prime_6719
    · exact prime_14891
  · decide +kernel

theorem prime_1245455169979 : Nat.Prime 1245455169979 := by
  apply nodeValid_prime [2, 3, 67, 3098147189] ⟨1245455169979, 3, [(2, 1), (3, 1), (67, 1), (3098147189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_3098147189
  · decide +kernel

theorem prime_1245455171047 : Nat.Prime 1245455171047 := by
  apply nodeValid_prime [2, 3, 61, 1307, 32143] ⟨1245455171047, 3, [(2, 1), (3, 5), (61, 1), (1307, 1), (32143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_1307
    · exact prime_32143
  · decide +kernel

theorem prime_1246967972609 : Nat.Prime 1246967972609 := by
  apply nodeValid_prime [2, 487, 1361, 7349] ⟨1246967972609, 3, [(2, 8), (487, 1), (1361, 1), (7349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_1361
    · exact prime_7349
  · decide +kernel

theorem prime_1246967973263 : Nat.Prime 1246967973263 := by
  apply nodeValid_prime [2, 11, 599, 94624979] ⟨1246967973263, 5, [(2, 1), (11, 1), (599, 1), (94624979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_599
    · exact prime_94624979
  · decide +kernel

theorem prime_1246967982427 : Nat.Prime 1246967982427 := by
  apply nodeValid_prime [2, 3, 207827997071] ⟨1246967982427, 2, [(2, 1), (3, 1), (207827997071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_207827997071
  · decide +kernel

theorem prime_1248482082553 : Nat.Prime 1248482082553 := by
  apply nodeValid_prime [2, 3, 89, 257, 331, 6871] ⟨1248482082553, 7, [(2, 3), (3, 1), (89, 1), (257, 1), (331, 1), (6871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_257
    · exact prime_331
    · exact prime_6871
  · decide +kernel

theorem prime_1248482088559 : Nat.Prime 1248482088559 := by
  apply nodeValid_prime [2, 3, 29, 265747571] ⟨1248482088559, 3, [(2, 1), (3, 4), (29, 1), (265747571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_265747571
  · decide +kernel

theorem prime_1249997420041 : Nat.Prime 1249997420041 := by
  apply nodeValid_prime [2, 3, 5, 83, 125501749] ⟨1249997420041, 7, [(2, 3), (3, 1), (5, 1), (83, 1), (125501749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_125501749
  · decide +kernel

theorem prime_1249997420141 : Nat.Prime 1249997420141 := by
  apply nodeValid_prime [2, 5, 7, 829, 10770269] ⟨1249997420141, 2, [(2, 2), (5, 1), (7, 1), (829, 1), (10770269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_829
    · exact prime_10770269
  · decide +kernel

theorem prime_1249997436917 : Nat.Prime 1249997436917 := by
  apply nodeValid_prime [2, 163, 1917173983] ⟨1249997436917, 2, [(2, 2), (163, 1), (1917173983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_1917173983
  · decide +kernel

theorem prime_1251513998909 : Nat.Prime 1251513998909 := by
  apply nodeValid_prime [2, 17, 353, 1741, 29947] ⟨1251513998909, 2, [(2, 2), (17, 1), (353, 1), (1741, 1), (29947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_353
    · exact prime_1741
    · exact prime_29947
  · decide +kernel

theorem prime_1251514030337 : Nat.Prime 1251514030337 := by
  apply nodeValid_prime [2, 397, 12314173] ⟨1251514030337, 3, [(2, 8), (397, 1), (12314173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_12314173
  · decide +kernel

theorem prime_1253031862003 : Nat.Prime 1253031862003 := by
  apply nodeValid_prime [2, 3, 23, 9079941029] ⟨1253031862003, 5, [(2, 1), (3, 1), (23, 1), (9079941029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_9079941029
  · decide +kernel

theorem prime_1253031862861 : Nat.Prime 1253031862861 := by
  apply nodeValid_prime [2, 3, 5, 53, 1949, 67391] ⟨1253031862861, 2, [(2, 2), (3, 2), (5, 1), (53, 1), (1949, 1), (67391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_1949
    · exact prime_67391
  · decide +kernel

theorem prime_1253031877843 : Nat.Prime 1253031877843 := by
  apply nodeValid_prime [2, 3, 59, 67, 163, 324113] ⟨1253031877843, 2, [(2, 1), (3, 1), (59, 1), (67, 1), (163, 1), (324113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_67
    · exact prime_163
    · exact prime_324113
  · decide +kernel

theorem prime_1254550983523 : Nat.Prime 1254550983523 := by
  apply nodeValid_prime [2, 3, 53, 3945128879] ⟨1254550983523, 2, [(2, 1), (3, 1), (53, 1), (3945128879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_3945128879
  · decide +kernel

theorem prime_1254551004677 : Nat.Prime 1254551004677 := by
  apply nodeValid_prime [2, 101, 3105324269] ⟨1254551004677, 2, [(2, 2), (101, 1), (3105324269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_3105324269
  · decide +kernel

theorem prime_1254551005399 : Nat.Prime 1254551005399 := by
  apply nodeValid_prime [2, 3, 577, 2833, 127913] ⟨1254551005399, 3, [(2, 1), (3, 1), (577, 1), (2833, 1), (127913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
    · exact prime_2833
    · exact prime_127913
  · decide +kernel

theorem prime_1256071336979 : Nat.Prime 1256071336979 := by
  apply nodeValid_prime [2, 17, 2173133801] ⟨1256071336979, 2, [(2, 1), (17, 2), (2173133801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2173133801
  · decide +kernel

theorem prime_1256071338583 : Nat.Prime 1256071338583 := by
  apply nodeValid_prime [2, 3, 53101, 3942397] ⟨1256071338583, 5, [(2, 1), (3, 1), (53101, 1), (3942397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53101
    · exact prime_3942397
  · decide +kernel

theorem prime_1256071338853 : Nat.Prime 1256071338853 := by
  apply nodeValid_prime [2, 3, 11, 29, 328127309] ⟨1256071338853, 5, [(2, 2), (3, 1), (11, 1), (29, 1), (328127309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_328127309
  · decide +kernel

theorem prime_1257592940839 : Nat.Prime 1257592940839 := by
  apply nodeValid_prime [2, 3, 13, 29, 185321683] ⟨1257592940839, 3, [(2, 1), (3, 2), (13, 1), (29, 1), (185321683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_185321683
  · decide +kernel

theorem prime_1257592983533 : Nat.Prime 1257592983533 := by
  apply nodeValid_prime [2, 2389, 131602447] ⟨1257592983533, 2, [(2, 2), (2389, 1), (131602447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2389
    · exact prime_131602447
  · decide +kernel

theorem prime_1257592983587 : Nat.Prime 1257592983587 := by
  apply nodeValid_prime [2, 17, 557, 66405797] ⟨1257592983587, 2, [(2, 1), (17, 1), (557, 1), (66405797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_557
    · exact prime_66405797
  · decide +kernel

theorem prime_1259115801701 : Nat.Prime 1259115801701 := by
  apply nodeValid_prime [2, 5, 83, 151700699] ⟨1259115801701, 2, [(2, 2), (5, 2), (83, 1), (151700699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_151700699
  · decide +kernel

theorem prime_1259115802363 : Nat.Prime 1259115802363 := by
  apply nodeValid_prime [2, 3, 11, 192702143] ⟨1259115802363, 2, [(2, 1), (3, 3), (11, 2), (192702143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_192702143
  · decide +kernel

theorem prime_1259115804127 : Nat.Prime 1259115804127 := by
  apply nodeValid_prime [2, 3, 251, 709, 393073] ⟨1259115804127, 3, [(2, 1), (3, 2), (251, 1), (709, 1), (393073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_709
    · exact prime_393073
  · decide +kernel

end Sude.Lucas.Generated
