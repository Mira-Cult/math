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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0081

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6043 : Nat.Prime 6043 := by
  apply nodeValid_prime [2, 3, 19, 53] ⟨6043, 5, [(2, 1), (3, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_11069 : Nat.Prime 11069 := by
  apply nodeValid_prime [2, 2767] ⟨11069, 2, [(2, 2), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2767
  · decide +kernel

theorem prime_11593 : Nat.Prime 11593 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨11593, 5, [(2, 3), (3, 2), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_15307 : Nat.Prime 15307 := by
  apply nodeValid_prime [2, 3, 2551] ⟨15307, 3, [(2, 1), (3, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2551
  · decide +kernel

theorem prime_16693 : Nat.Prime 16693 := by
  apply nodeValid_prime [2, 3, 13, 107] ⟨16693, 2, [(2, 2), (3, 1), (13, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_107
  · decide +kernel

theorem prime_16871 : Nat.Prime 16871 := by
  apply nodeValid_prime [2, 5, 7, 241] ⟨16871, 17, [(2, 1), (5, 1), (7, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_241
  · decide +kernel

theorem prime_17827 : Nat.Prime 17827 := by
  apply nodeValid_prime [2, 3, 2971] ⟨17827, 2, [(2, 1), (3, 1), (2971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2971
  · decide +kernel

theorem prime_19429 : Nat.Prime 19429 := by
  apply nodeValid_prime [2, 3, 1619] ⟨19429, 6, [(2, 2), (3, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1619
  · decide +kernel

theorem prime_26183 : Nat.Prime 26183 := by
  apply nodeValid_prime [2, 13, 19, 53] ⟨26183, 5, [(2, 1), (13, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_27481 : Nat.Prime 27481 := by
  apply nodeValid_prime [2, 3, 5, 229] ⟨27481, 7, [(2, 3), (3, 1), (5, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
  · decide +kernel

theorem prime_33479 : Nat.Prime 33479 := by
  apply nodeValid_prime [2, 19, 881] ⟨33479, 17, [(2, 1), (19, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_881
  · decide +kernel

theorem prime_36263 : Nat.Prime 36263 := by
  apply nodeValid_prime [2, 18131] ⟨36263, 5, [(2, 1), (18131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18131
  · decide +kernel

theorem prime_46663 : Nat.Prime 46663 := by
  apply nodeValid_prime [2, 3, 7, 11, 101] ⟨46663, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_101
  · decide +kernel

theorem prime_47947 : Nat.Prime 47947 := by
  apply nodeValid_prime [2, 3, 61, 131] ⟨47947, 2, [(2, 1), (3, 1), (61, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_131
  · decide +kernel

theorem prime_53861 : Nat.Prime 53861 := by
  apply nodeValid_prime [2, 5, 2693] ⟨53861, 2, [(2, 2), (5, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2693
  · decide +kernel

theorem prime_54347 : Nat.Prime 54347 := by
  apply nodeValid_prime [2, 29, 937] ⟨54347, 2, [(2, 1), (29, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_937
  · decide +kernel

theorem prime_63541 : Nat.Prime 63541 := by
  apply nodeValid_prime [2, 3, 5, 353] ⟨63541, 2, [(2, 2), (3, 2), (5, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
  · decide +kernel

theorem prime_65629 : Nat.Prime 65629 := by
  apply nodeValid_prime [2, 3, 1823] ⟨65629, 2, [(2, 2), (3, 2), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1823
  · decide +kernel

theorem prime_66959 : Nat.Prime 66959 := by
  apply nodeValid_prime [2, 33479] ⟨66959, 7, [(2, 1), (33479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33479
  · decide +kernel

theorem prime_84011 : Nat.Prime 84011 := by
  apply nodeValid_prime [2, 5, 31, 271] ⟨84011, 6, [(2, 1), (5, 1), (31, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_271
  · decide +kernel

theorem prime_84857 : Nat.Prime 84857 := by
  apply nodeValid_prime [2, 10607] ⟨84857, 3, [(2, 3), (10607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10607
  · decide +kernel

theorem prime_92363 : Nat.Prime 92363 := by
  apply nodeValid_prime [2, 46181] ⟨92363, 2, [(2, 1), (46181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46181
  · decide +kernel

theorem prime_98317 : Nat.Prime 98317 := by
  apply nodeValid_prime [2, 3, 2731] ⟨98317, 6, [(2, 2), (3, 2), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2731
  · decide +kernel

theorem prime_102397 : Nat.Prime 102397 := by
  apply nodeValid_prime [2, 3, 7, 23, 53] ⟨102397, 5, [(2, 2), (3, 1), (7, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_108233 : Nat.Prime 108233 := by
  apply nodeValid_prime [2, 83, 163] ⟨108233, 3, [(2, 3), (83, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_163
  · decide +kernel

theorem prime_117721 : Nat.Prime 117721 := by
  apply nodeValid_prime [2, 3, 5, 109] ⟨117721, 22, [(2, 3), (3, 3), (5, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
  · decide +kernel

theorem prime_124097 : Nat.Prime 124097 := by
  apply nodeValid_prime [2, 7, 277] ⟨124097, 3, [(2, 6), (7, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_130681 : Nat.Prime 130681 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨130681, 7, [(2, 3), (3, 3), (5, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_134947 : Nat.Prime 134947 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨134947, 13, [(2, 1), (3, 4), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_147881 : Nat.Prime 147881 := by
  apply nodeValid_prime [2, 5, 3697] ⟨147881, 3, [(2, 3), (5, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3697
  · decide +kernel

theorem prime_159431 : Nat.Prime 159431 := by
  apply nodeValid_prime [2, 5, 107, 149] ⟨159431, 23, [(2, 1), (5, 1), (107, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_149
  · decide +kernel

theorem prime_159871 : Nat.Prime 159871 := by
  apply nodeValid_prime [2, 3, 5, 73] ⟨159871, 6, [(2, 1), (3, 1), (5, 1), (73, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_184727 : Nat.Prime 184727 := by
  apply nodeValid_prime [2, 92363] ⟨184727, 5, [(2, 1), (92363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92363
  · decide +kernel

theorem prime_196307 : Nat.Prime 196307 := by
  apply nodeValid_prime [2, 11, 8923] ⟨196307, 2, [(2, 1), (11, 1), (8923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8923
  · decide +kernel

theorem prime_218657 : Nat.Prime 218657 := by
  apply nodeValid_prime [2, 6833] ⟨218657, 3, [(2, 5), (6833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6833
  · decide +kernel

theorem prime_248203 : Nat.Prime 248203 := by
  apply nodeValid_prime [2, 3, 13789] ⟨248203, 5, [(2, 1), (3, 2), (13789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13789
  · decide +kernel

theorem prime_256133 : Nat.Prime 256133 := by
  apply nodeValid_prime [2, 64033] ⟨256133, 2, [(2, 2), (64033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_64033
  · decide +kernel

theorem prime_265333 : Nat.Prime 265333 := by
  apply nodeValid_prime [2, 3, 22111] ⟨265333, 6, [(2, 2), (3, 1), (22111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22111
  · decide +kernel

theorem prime_318863 : Nat.Prime 318863 := by
  apply nodeValid_prime [2, 159431] ⟨318863, 5, [(2, 1), (159431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_159431
  · decide +kernel

theorem prime_338137 : Nat.Prime 338137 := by
  apply nodeValid_prime [2, 3, 73, 193] ⟨338137, 5, [(2, 3), (3, 1), (73, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_193
  · decide +kernel

theorem prime_391403 : Nat.Prime 391403 := by
  apply nodeValid_prime [2, 11, 17791] ⟨391403, 2, [(2, 1), (11, 1), (17791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17791
  · decide +kernel

theorem prime_395971 : Nat.Prime 395971 := by
  apply nodeValid_prime [2, 3, 5, 67, 197] ⟨395971, 2, [(2, 1), (3, 1), (5, 1), (67, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_197
  · decide +kernel

theorem prime_418447 : Nat.Prime 418447 := by
  apply nodeValid_prime [2, 3, 7, 41] ⟨418447, 6, [(2, 1), (3, 6), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_448807 : Nat.Prime 448807 := by
  apply nodeValid_prime [2, 3, 131, 571] ⟨448807, 5, [(2, 1), (3, 1), (131, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_571
  · decide +kernel

theorem prime_488651 : Nat.Prime 488651 := by
  apply nodeValid_prime [2, 5, 29, 337] ⟨488651, 2, [(2, 1), (5, 2), (29, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_337
  · decide +kernel

theorem prime_518737 : Nat.Prime 518737 := by
  apply nodeValid_prime [2, 3, 101, 107] ⟨518737, 5, [(2, 4), (3, 1), (101, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_107
  · decide +kernel

theorem prime_629401 : Nat.Prime 629401 := by
  apply nodeValid_prime [2, 3, 5, 1049] ⟨629401, 13, [(2, 3), (3, 1), (5, 2), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1049
  · decide +kernel

theorem prime_649469 : Nat.Prime 649469 := by
  apply nodeValid_prime [2, 17, 9551] ⟨649469, 2, [(2, 2), (17, 1), (9551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9551
  · decide +kernel

theorem prime_695581 : Nat.Prime 695581 := by
  apply nodeValid_prime [2, 3, 5, 11593] ⟨695581, 6, [(2, 2), (3, 1), (5, 1), (11593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11593
  · decide +kernel

theorem prime_698051 : Nat.Prime 698051 := by
  apply nodeValid_prime [2, 5, 23, 607] ⟨698051, 6, [(2, 1), (5, 2), (23, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_607
  · decide +kernel

theorem prime_700523 : Nat.Prime 700523 := by
  apply nodeValid_prime [2, 227, 1543] ⟨700523, 2, [(2, 1), (227, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_1543
  · decide +kernel

theorem prime_760267 : Nat.Prime 760267 := by
  apply nodeValid_prime [2, 3, 13, 19] ⟨760267, 3, [(2, 1), (3, 4), (13, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_1013899 : Nat.Prime 1013899 := by
  apply nodeValid_prime [2, 3, 29, 5827] ⟨1013899, 3, [(2, 1), (3, 1), (29, 1), (5827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_5827
  · decide +kernel

theorem prime_1108363 : Nat.Prime 1108363 := by
  apply nodeValid_prime [2, 3, 184727] ⟨1108363, 2, [(2, 1), (3, 1), (184727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_184727
  · decide +kernel

theorem prime_1518827 : Nat.Prime 1518827 := by
  apply nodeValid_prime [2, 97, 7829] ⟨1518827, 2, [(2, 1), (97, 1), (7829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_7829
  · decide +kernel

theorem prime_1764281 : Nat.Prime 1764281 := by
  apply nodeValid_prime [2, 5, 7, 6301] ⟨1764281, 11, [(2, 3), (5, 1), (7, 1), (6301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6301
  · decide +kernel

theorem prime_2483753 : Nat.Prime 2483753 := by
  apply nodeValid_prime [2, 73, 4253] ⟨2483753, 3, [(2, 3), (73, 1), (4253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_4253
  · decide +kernel

theorem prime_2575549 : Nat.Prime 2575549 := by
  apply nodeValid_prime [2, 3, 29, 2467] ⟨2575549, 2, [(2, 2), (3, 2), (29, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2467
  · decide +kernel

theorem prime_2627393 : Nat.Prime 2627393 := by
  apply nodeValid_prime [2, 61, 673] ⟨2627393, 3, [(2, 6), (61, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_673
  · decide +kernel

theorem prime_2638177 : Nat.Prime 2638177 := by
  apply nodeValid_prime [2, 3, 27481] ⟨2638177, 10, [(2, 5), (3, 1), (27481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27481
  · decide +kernel

theorem prime_2919557 : Nat.Prime 2919557 := by
  apply nodeValid_prime [2, 59, 89, 139] ⟨2919557, 2, [(2, 2), (59, 1), (89, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_89
    · exact prime_139
  · decide +kernel

theorem prime_3766691 : Nat.Prime 3766691 := by
  apply nodeValid_prime [2, 5, 17, 22157] ⟨3766691, 2, [(2, 1), (5, 1), (17, 1), (22157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_22157
  · decide +kernel

theorem prime_3909209 : Nat.Prime 3909209 := by
  apply nodeValid_prime [2, 488651] ⟨3909209, 3, [(2, 3), (488651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_488651
  · decide +kernel

theorem prime_4934399 : Nat.Prime 4934399 := by
  apply nodeValid_prime [2, 7, 7193] ⟨4934399, 7, [(2, 1), (7, 3), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7193
  · decide +kernel

theorem prime_5591309 : Nat.Prime 5591309 := by
  apply nodeValid_prime [2, 47, 29741] ⟨5591309, 2, [(2, 2), (47, 1), (29741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_29741
  · decide +kernel

theorem prime_6294011 : Nat.Prime 6294011 := by
  apply nodeValid_prime [2, 5, 629401] ⟨6294011, 2, [(2, 1), (5, 1), (629401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_629401
  · decide +kernel

theorem prime_6582889 : Nat.Prime 6582889 := by
  apply nodeValid_prime [2, 3, 13, 541] ⟨6582889, 7, [(2, 3), (3, 2), (13, 2), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_541
  · decide +kernel

theorem prime_6708017 : Nat.Prime 6708017 := by
  apply nodeValid_prime [2, 7, 101, 593] ⟨6708017, 3, [(2, 4), (7, 1), (101, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_593
  · decide +kernel

theorem prime_6795413 : Nat.Prime 6795413 := by
  apply nodeValid_prime [2, 13, 130681] ⟨6795413, 2, [(2, 2), (13, 1), (130681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_130681
  · decide +kernel

theorem prime_8299793 : Nat.Prime 8299793 := by
  apply nodeValid_prime [2, 518737] ⟨8299793, 3, [(2, 4), (518737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_518737
  · decide +kernel

theorem prime_9369419 : Nat.Prime 9369419 := by
  apply nodeValid_prime [2, 23, 149, 1367] ⟨9369419, 2, [(2, 1), (23, 1), (149, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_149
    · exact prime_1367
  · decide +kernel

theorem prime_9868799 : Nat.Prime 9868799 := by
  apply nodeValid_prime [2, 4934399] ⟨9868799, 13, [(2, 1), (4934399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4934399
  · decide +kernel

theorem prime_10128451 : Nat.Prime 10128451 := by
  apply nodeValid_prime [2, 3, 5, 67523] ⟨10128451, 7, [(2, 1), (3, 1), (5, 2), (67523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67523
  · decide +kernel

theorem prime_10552709 : Nat.Prime 10552709 := by
  apply nodeValid_prime [2, 2638177] ⟨10552709, 2, [(2, 2), (2638177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2638177
  · decide +kernel

theorem prime_10887623 : Nat.Prime 10887623 := by
  apply nodeValid_prime [2, 79, 68909] ⟨10887623, 5, [(2, 1), (79, 1), (68909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_68909
  · decide +kernel

theorem prime_12755909 : Nat.Prime 12755909 := by
  apply nodeValid_prime [2, 11, 239, 1213] ⟨12755909, 2, [(2, 2), (11, 1), (239, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_1213
  · decide +kernel

theorem prime_16302161 : Nat.Prime 16302161 := by
  apply nodeValid_prime [2, 5, 7, 43, 677] ⟨16302161, 3, [(2, 4), (5, 1), (7, 1), (43, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_677
  · decide +kernel

theorem prime_17517343 : Nat.Prime 17517343 := by
  apply nodeValid_prime [2, 3, 2919557] ⟨17517343, 3, [(2, 1), (3, 1), (2919557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2919557
  · decide +kernel

theorem prime_20165309 : Nat.Prime 20165309 := by
  apply nodeValid_prime [2, 19, 265333] ⟨20165309, 2, [(2, 2), (19, 1), (265333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_265333
  · decide +kernel

theorem prime_21105419 : Nat.Prime 21105419 := by
  apply nodeValid_prime [2, 10552709] ⟨21105419, 2, [(2, 1), (10552709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10552709
  · decide +kernel

theorem prime_21836413 : Nat.Prime 21836413 := by
  apply nodeValid_prime [2, 3, 13, 103, 151] ⟨21836413, 6, [(2, 2), (3, 3), (13, 1), (103, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
    · exact prime_151
  · decide +kernel

theorem prime_23099603 : Nat.Prime 23099603 := by
  apply nodeValid_prime [2, 29, 61, 6529] ⟨23099603, 5, [(2, 1), (29, 1), (61, 1), (6529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_61
    · exact prime_6529
  · decide +kernel

theorem prime_23547949 : Nat.Prime 23547949 := by
  apply nodeValid_prime [2, 3, 101, 19429] ⟨23547949, 2, [(2, 2), (3, 1), (101, 1), (19429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_19429
  · decide +kernel

theorem prime_25511819 : Nat.Prime 25511819 := by
  apply nodeValid_prime [2, 12755909] ⟨25511819, 2, [(2, 1), (12755909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12755909
  · decide +kernel

theorem prime_25657943 : Nat.Prime 25657943 := by
  apply nodeValid_prime [2, 19, 61, 11069] ⟨25657943, 5, [(2, 1), (19, 1), (61, 1), (11069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
    · exact prime_11069
  · decide +kernel

theorem prime_35659097 : Nat.Prime 35659097 := by
  apply nodeValid_prime [2, 11, 29, 89, 157] ⟨35659097, 3, [(2, 3), (11, 1), (29, 1), (89, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_89
    · exact prime_157
  · decide +kernel

theorem prime_37302767 : Nat.Prime 37302767 := by
  apply nodeValid_prime [2, 389, 47947] ⟨37302767, 5, [(2, 1), (389, 1), (47947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_389
    · exact prime_47947
  · decide +kernel

theorem prime_41806367 : Nat.Prime 41806367 := by
  apply nodeValid_prime [2, 7, 17, 269, 653] ⟨41806367, 5, [(2, 1), (7, 1), (17, 1), (269, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_269
    · exact prime_653
  · decide +kernel

theorem prime_69362759 : Nat.Prime 69362759 := by
  apply nodeValid_prime [2, 257, 134947] ⟨69362759, 7, [(2, 1), (257, 1), (134947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_134947
  · decide +kernel

theorem prime_131520937 : Nat.Prime 131520937 := by
  apply nodeValid_prime [2, 3, 569, 9631] ⟨131520937, 5, [(2, 3), (3, 1), (569, 1), (9631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
    · exact prime_9631
  · decide +kernel

theorem prime_184938073 : Nat.Prime 184938073 := by
  apply nodeValid_prime [2, 3, 11, 700523] ⟨184938073, 5, [(2, 3), (3, 1), (11, 1), (700523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_700523
  · decide +kernel

theorem prime_216124127 : Nat.Prime 216124127 := by
  apply nodeValid_prime [2, 19, 31, 271, 677] ⟨216124127, 5, [(2, 1), (19, 1), (31, 1), (271, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_271
    · exact prime_677
  · decide +kernel

theorem prime_404874653 : Nat.Prime 404874653 := by
  apply nodeValid_prime [2, 7, 13, 17, 719] ⟨404874653, 2, [(2, 2), (7, 2), (13, 2), (17, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_719
  · decide +kernel

theorem prime_518054879 : Nat.Prime 518054879 := by
  apply nodeValid_prime [2, 11, 23547949] ⟨518054879, 11, [(2, 1), (11, 1), (23547949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23547949
  · decide +kernel

theorem prime_558770969 : Nat.Prime 558770969 := by
  apply nodeValid_prime [2, 7, 47, 4517] ⟨558770969, 3, [(2, 3), (7, 1), (47, 2), (4517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_4517
  · decide +kernel

theorem prime_693184183 : Nat.Prime 693184183 := by
  apply nodeValid_prime [2, 3, 19, 1321, 4603] ⟨693184183, 3, [(2, 1), (3, 1), (19, 1), (1321, 1), (4603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1321
    · exact prime_4603
  · decide +kernel

theorem prime_876403097 : Nat.Prime 876403097 := by
  apply nodeValid_prime [2, 1291, 84857] ⟨876403097, 3, [(2, 3), (1291, 1), (84857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1291
    · exact prime_84857
  · decide +kernel

theorem prime_1008592451 : Nat.Prime 1008592451 := by
  apply nodeValid_prime [2, 5, 29, 695581] ⟨1008592451, 2, [(2, 1), (5, 2), (29, 1), (695581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_695581
  · decide +kernel

theorem prime_1494596581 : Nat.Prime 1494596581 := by
  apply nodeValid_prime [2, 3, 5, 23, 43, 89, 283] ⟨1494596581, 6, [(2, 2), (3, 1), (5, 1), (23, 1), (43, 1), (89, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_43
    · exact prime_89
    · exact prime_283
  · decide +kernel

theorem prime_2052214727 : Nat.Prime 2052214727 := by
  apply nodeValid_prime [2, 151, 6795413] ⟨2052214727, 5, [(2, 1), (151, 1), (6795413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_6795413
  · decide +kernel

theorem prime_2117021113 : Nat.Prime 2117021113 := by
  apply nodeValid_prime [2, 3, 29, 1013899] ⟨2117021113, 5, [(2, 3), (3, 2), (29, 1), (1013899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1013899
  · decide +kernel

theorem prime_2384646917 : Nat.Prime 2384646917 := by
  apply nodeValid_prime [2, 17, 29, 79, 15307] ⟨2384646917, 2, [(2, 2), (17, 1), (29, 1), (79, 1), (15307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_79
    · exact prime_15307
  · decide +kernel

theorem prime_2959009169 : Nat.Prime 2959009169 := by
  apply nodeValid_prime [2, 184938073] ⟨2959009169, 3, [(2, 4), (184938073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_184938073
  · decide +kernel

theorem prime_3153500531 : Nat.Prime 3153500531 := by
  apply nodeValid_prime [2, 5, 53, 61, 103, 947] ⟨3153500531, 2, [(2, 1), (5, 1), (53, 1), (61, 1), (103, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_61
    · exact prime_103
    · exact prime_947
  · decide +kernel

theorem prime_3266780059 : Nat.Prime 3266780059 := by
  apply nodeValid_prime [2, 3, 20165309] ⟨3266780059, 2, [(2, 1), (3, 4), (20165309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20165309
  · decide +kernel

theorem prime_6073480631 : Nat.Prime 6073480631 := by
  apply nodeValid_prime [2, 5, 7, 31, 157, 17827] ⟨6073480631, 11, [(2, 1), (5, 1), (7, 1), (31, 1), (157, 1), (17827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_157
    · exact prime_17827
  · decide +kernel

theorem prime_6490681459 : Nat.Prime 6490681459 := by
  apply nodeValid_prime [2, 3, 29, 37302767] ⟨6490681459, 2, [(2, 1), (3, 1), (29, 1), (37302767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_37302767
  · decide +kernel

theorem prime_6605199697 : Nat.Prime 6605199697 := by
  apply nodeValid_prime [2, 3, 181, 760267] ⟨6605199697, 5, [(2, 4), (3, 1), (181, 1), (760267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_760267
  · decide +kernel

theorem prime_20747916193 : Nat.Prime 20747916193 := by
  apply nodeValid_prime [2, 3, 216124127] ⟨20747916193, 10, [(2, 5), (3, 1), (216124127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_216124127
  · decide +kernel

theorem prime_21890140621 : Nat.Prime 21890140621 := by
  apply nodeValid_prime [2, 3, 5, 73, 1783, 2803] ⟨21890140621, 2, [(2, 2), (3, 1), (5, 1), (73, 1), (1783, 1), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_1783
    · exact prime_2803
  · decide +kernel

theorem prime_25321657957 : Nat.Prime 25321657957 := by
  apply nodeValid_prime [2, 3, 7, 31, 523, 18593] ⟨25321657957, 11, [(2, 2), (3, 1), (7, 1), (31, 1), (523, 1), (18593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_523
    · exact prime_18593
  · decide +kernel

theorem prime_25962725837 : Nat.Prime 25962725837 := by
  apply nodeValid_prime [2, 6490681459] ⟨25962725837, 2, [(2, 2), (6490681459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6490681459
  · decide +kernel

theorem prime_34224994933 : Nat.Prime 34224994933 := by
  apply nodeValid_prime [2, 3, 17, 9868799] ⟨34224994933, 2, [(2, 2), (3, 1), (17, 2), (9868799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9868799
  · decide +kernel

theorem prime_39631198193 : Nat.Prime 39631198193 := by
  apply nodeValid_prime [2, 443, 5591309] ⟨39631198193, 3, [(2, 4), (443, 1), (5591309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_5591309
  · decide +kernel

theorem prime_100169455663 : Nat.Prime 100169455663 := by
  apply nodeValid_prime [2, 3, 54347, 102397] ⟨100169455663, 3, [(2, 1), (3, 2), (54347, 1), (102397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54347
    · exact prime_102397
  · decide +kernel

theorem prime_123048711229 : Nat.Prime 123048711229 := by
  apply nodeValid_prime [2, 3, 17, 37, 16302161] ⟨123048711229, 2, [(2, 2), (3, 1), (17, 1), (37, 1), (16302161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_16302161
  · decide +kernel

theorem prime_183644009291 : Nat.Prime 183644009291 := by
  apply nodeValid_prime [2, 5, 7, 1487, 1764281] ⟨183644009291, 2, [(2, 1), (5, 1), (7, 1), (1487, 1), (1764281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1487
    · exact prime_1764281
  · decide +kernel

theorem prime_185692153099 : Nat.Prime 185692153099 := by
  apply nodeValid_prime [2, 3, 71, 8093, 53861] ⟨185692153099, 2, [(2, 1), (3, 1), (71, 1), (8093, 1), (53861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_8093
    · exact prime_53861
  · decide +kernel

theorem prime_367288018583 : Nat.Prime 367288018583 := by
  apply nodeValid_prime [2, 183644009291] ⟨367288018583, 5, [(2, 1), (183644009291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_183644009291
  · decide +kernel

theorem prime_548709111553 : Nat.Prime 548709111553 := by
  apply nodeValid_prime [2, 3, 7, 2269, 44983] ⟨548709111553, 10, [(2, 8), (3, 1), (7, 1), (2269, 1), (44983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2269
    · exact prime_44983
  · decide +kernel

theorem prime_1115274666101 : Nat.Prime 1115274666101 := by
  apply nodeValid_prime [2, 5, 7, 1049, 1518827] ⟨1115274666101, 17, [(2, 2), (5, 2), (7, 1), (1049, 1), (1518827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1049
    · exact prime_1518827
  · decide +kernel

theorem prime_2190399675713 : Nat.Prime 2190399675713 := by
  apply nodeValid_prime [2, 34224994933] ⟨2190399675713, 3, [(2, 6), (34224994933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34224994933
  · decide +kernel

theorem prime_2190399766949 : Nat.Prime 2190399766949 := by
  apply nodeValid_prime [2, 23, 131, 1229, 147881] ⟨2190399766949, 2, [(2, 2), (23, 1), (131, 1), (1229, 1), (147881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_131
    · exact prime_1229
    · exact prime_147881
  · decide +kernel

theorem prime_2190399767051 : Nat.Prime 2190399767051 := by
  apply nodeValid_prime [2, 5, 11, 29, 211, 787, 827] ⟨2190399767051, 2, [(2, 1), (5, 2), (11, 1), (29, 1), (211, 1), (787, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_211
    · exact prime_787
    · exact prime_827
  · decide +kernel

theorem prime_2192617261147 : Nat.Prime 2192617261147 := by
  apply nodeValid_prime [2, 3, 13, 823, 2627393] ⟨2192617261147, 2, [(2, 1), (3, 1), (13, 2), (823, 1), (2627393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_823
    · exact prime_2627393
  · decide +kernel

theorem prime_2192617281857 : Nat.Prime 2192617281857 := by
  apply nodeValid_prime [2, 17, 2887, 698051] ⟨2192617281857, 3, [(2, 6), (17, 1), (2887, 1), (698051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2887
    · exact prime_698051
  · decide +kernel

theorem prime_2192617282357 : Nat.Prime 2192617282357 := by
  apply nodeValid_prime [2, 3, 109, 558770969] ⟨2192617282357, 2, [(2, 2), (3, 2), (109, 1), (558770969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_558770969
  · decide +kernel

theorem prime_2194836369577 : Nat.Prime 2194836369577 := by
  apply nodeValid_prime [2, 3, 29, 3153500531] ⟨2194836369577, 7, [(2, 3), (3, 1), (29, 1), (3153500531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_3153500531
  · decide +kernel

theorem prime_2194836446213 : Nat.Prime 2194836446213 := by
  apply nodeValid_prime [2, 548709111553] ⟨2194836446213, 2, [(2, 2), (548709111553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_548709111553
  · decide +kernel

theorem prime_2194836446617 : Nat.Prime 2194836446617 := by
  apply nodeValid_prime [2, 3, 11, 23, 1069, 338137] ⟨2194836446617, 7, [(2, 3), (3, 1), (11, 1), (23, 1), (1069, 1), (338137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_1069
    · exact prime_338137
  · decide +kernel

theorem prime_2197056972631 : Nat.Prime 2197056972631 := by
  apply nodeValid_prime [2, 3, 5, 13, 41, 347, 395971] ⟨2197056972631, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (41, 1), (347, 1), (395971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_347
    · exact prime_395971
  · decide +kernel

theorem prime_2197056974071 : Nat.Prime 2197056974071 := by
  apply nodeValid_prime [2, 3, 5, 7, 1494596581] ⟨2197056974071, 12, [(2, 1), (3, 1), (5, 1), (7, 2), (1494596581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1494596581
  · decide +kernel

theorem prime_2197056995663 : Nat.Prime 2197056995663 := by
  apply nodeValid_prime [2, 163, 619, 10887623] ⟨2197056995663, 5, [(2, 1), (163, 1), (619, 1), (10887623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_619
    · exact prime_10887623
  · decide +kernel

theorem prime_2199279115097 : Nat.Prime 2199279115097 := by
  apply nodeValid_prime [2, 7, 97, 404874653] ⟨2199279115097, 5, [(2, 3), (7, 1), (97, 1), (404874653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_97
    · exact prime_404874653
  · decide +kernel

theorem prime_2199279116459 : Nat.Prime 2199279116459 := by
  apply nodeValid_prime [2, 53, 20747916193] ⟨2199279116459, 2, [(2, 1), (53, 1), (20747916193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_20747916193
  · decide +kernel

theorem prime_2199279149141 : Nat.Prime 2199279149141 := by
  apply nodeValid_prime [2, 5, 13249, 8299793] ⟨2199279149141, 2, [(2, 2), (5, 1), (13249, 1), (8299793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13249
    · exact prime_8299793
  · decide +kernel

theorem prime_2201502821737 : Nat.Prime 2201502821737 := by
  apply nodeValid_prime [2, 3, 31, 2959009169] ⟨2201502821737, 5, [(2, 3), (3, 1), (31, 1), (2959009169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2959009169
  · decide +kernel

theorem prime_2201502822007 : Nat.Prime 2201502822007 := by
  apply nodeValid_prime [2, 3, 29, 3359, 3766691] ⟨2201502822007, 3, [(2, 1), (3, 1), (29, 1), (3359, 1), (3766691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_3359
    · exact prime_3766691
  · decide +kernel

theorem prime_2201502825287 : Nat.Prime 2201502825287 := by
  apply nodeValid_prime [2, 42901, 25657943] ⟨2201502825287, 5, [(2, 1), (42901, 1), (25657943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_42901
    · exact prime_25657943
  · decide +kernel

theorem prime_2203728024587 : Nat.Prime 2203728024587 := by
  apply nodeValid_prime [2, 11, 100169455663] ⟨2203728024587, 2, [(2, 1), (11, 1), (100169455663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_100169455663
  · decide +kernel

theorem prime_2203728111499 : Nat.Prime 2203728111499 := by
  apply nodeValid_prime [2, 3, 367288018583] ⟨2203728111499, 2, [(2, 1), (3, 1), (367288018583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367288018583
  · decide +kernel

theorem prime_2203728111679 : Nat.Prime 2203728111679 := by
  apply nodeValid_prime [2, 3, 36263, 10128451] ⟨2203728111679, 3, [(2, 1), (3, 1), (36263, 1), (10128451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36263
    · exact prime_10128451
  · decide +kernel

theorem prime_2205954748199 : Nat.Prime 2205954748199 := by
  apply nodeValid_prime [2, 117721, 9369419] ⟨2205954748199, 11, [(2, 1), (117721, 1), (9369419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_117721
    · exact prime_9369419
  · decide +kernel

theorem prime_2205954761123 : Nat.Prime 2205954761123 := by
  apply nodeValid_prime [2, 7, 3769, 41806367] ⟨2205954761123, 2, [(2, 1), (7, 1), (3769, 1), (41806367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3769
    · exact prime_41806367
  · decide +kernel

theorem prime_2205954761891 : Nat.Prime 2205954761891 := by
  apply nodeValid_prime [2, 5, 11, 37, 251, 196307] ⟨2205954761891, 2, [(2, 1), (5, 1), (11, 2), (37, 1), (251, 1), (196307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_251
    · exact prime_196307
  · decide +kernel

theorem prime_2208182992837 : Nat.Prime 2208182992837 := by
  apply nodeValid_prime [2, 3, 37, 1931, 2575549] ⟨2208182992837, 5, [(2, 2), (3, 1), (37, 1), (1931, 1), (2575549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1931
    · exact prime_2575549
  · decide +kernel

theorem prime_2208183045143 : Nat.Prime 2208183045143 := by
  apply nodeValid_prime [2, 463, 2384646917] ⟨2208183045143, 5, [(2, 1), (463, 1), (2384646917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_463
    · exact prime_2384646917
  · decide +kernel

theorem prime_2208183046253 : Nat.Prime 2208183046253 := by
  apply nodeValid_prime [2, 269, 2052214727] ⟨2208183046253, 2, [(2, 2), (269, 1), (2052214727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_2052214727
  · decide +kernel

theorem prime_2210412742339 : Nat.Prime 2210412742339 := by
  apply nodeValid_prime [2, 3, 16871, 21836413] ⟨2210412742339, 2, [(2, 1), (3, 1), (16871, 1), (21836413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16871
    · exact prime_21836413
  · decide +kernel

theorem prime_2210412742709 : Nat.Prime 2210412742709 := by
  apply nodeValid_prime [2, 26183, 21105419] ⟨2210412742709, 2, [(2, 2), (26183, 1), (21105419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_26183
    · exact prime_21105419
  · decide +kernel

theorem prime_2210412764353 : Nat.Prime 2210412764353 := by
  apply nodeValid_prime [2, 3, 13, 17, 47, 1108363] ⟨2210412764353, 5, [(2, 6), (3, 1), (13, 1), (17, 1), (47, 1), (1108363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_47
    · exact prime_1108363
  · decide +kernel

theorem prime_2212643911759 : Nat.Prime 2212643911759 := by
  apply nodeValid_prime [2, 3, 7, 2393, 3169, 6947] ⟨2212643911759, 3, [(2, 1), (3, 1), (7, 1), (2393, 1), (3169, 1), (6947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2393
    · exact prime_3169
    · exact prime_6947
  · decide +kernel

theorem prime_2212643912137 : Nat.Prime 2212643912137 := by
  apply nodeValid_prime [2, 3, 7, 19, 693184183] ⟨2212643912137, 5, [(2, 3), (3, 1), (7, 1), (19, 1), (693184183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_693184183
  · decide +kernel

theorem prime_2212644060103 : Nat.Prime 2212644060103 := by
  apply nodeValid_prime [2, 3, 7, 29, 31, 53, 997, 1109] ⟨2212644060103, 5, [(2, 1), (3, 1), (7, 1), (29, 1), (31, 1), (53, 1), (997, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_31
    · exact prime_53
    · exact prime_997
    · exact prime_1109
  · decide +kernel

theorem prime_2214876802123 : Nat.Prime 2214876802123 := by
  apply nodeValid_prime [2, 3, 123048711229] ⟨2214876802123, 13, [(2, 1), (3, 2), (123048711229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_123048711229
  · decide +kernel

theorem prime_2214876802739 : Nat.Prime 2214876802739 := by
  apply nodeValid_prime [2, 19, 31, 757, 2483753] ⟨2214876802739, 2, [(2, 1), (19, 1), (31, 1), (757, 1), (2483753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_757
    · exact prime_2483753
  · decide +kernel

theorem prime_2214876880003 : Nat.Prime 2214876880003 := by
  apply nodeValid_prime [2, 3, 113, 3266780059] ⟨2214876880003, 2, [(2, 1), (3, 1), (113, 1), (3266780059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_3266780059
  · decide +kernel

theorem prime_2217111203519 : Nat.Prime 2217111203519 := by
  apply nodeValid_prime [2, 389, 479, 1733, 3433] ⟨2217111203519, 7, [(2, 1), (389, 1), (479, 1), (1733, 1), (3433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_389
    · exact prime_479
    · exact prime_1733
    · exact prime_3433
  · decide +kernel

theorem prime_2217111204929 : Nat.Prime 2217111204929 := by
  apply nodeValid_prime [2, 31, 43, 409, 63541] ⟨2217111204929, 3, [(2, 6), (31, 1), (43, 1), (409, 1), (63541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_409
    · exact prime_63541
  · decide +kernel

theorem prime_2217111228677 : Nat.Prime 2217111228677 := by
  apply nodeValid_prime [2, 61, 131, 69362759] ⟨2217111228677, 2, [(2, 2), (61, 1), (131, 1), (69362759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_131
    · exact prime_69362759
  · decide +kernel

theorem prime_2219347098193 : Nat.Prime 2219347098193 := by
  apply nodeValid_prime [2, 3, 7, 6605199697] ⟨2219347098193, 5, [(2, 4), (3, 1), (7, 1), (6605199697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6605199697
  · decide +kernel

theorem prime_2219347098809 : Nat.Prime 2219347098809 := by
  apply nodeValid_prime [2, 7, 39631198193] ⟨2219347098809, 3, [(2, 3), (7, 1), (39631198193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_39631198193
  · decide +kernel

theorem prime_2219347101637 : Nat.Prime 2219347101637 := by
  apply nodeValid_prime [2, 3, 7, 17, 518054879] ⟨2219347101637, 5, [(2, 2), (3, 2), (7, 1), (17, 1), (518054879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_518054879
  · decide +kernel

theorem prime_2221584473947 : Nat.Prime 2221584473947 := by
  apply nodeValid_prime [2, 3, 23, 919, 17517343] ⟨2221584473947, 5, [(2, 1), (3, 1), (23, 1), (919, 1), (17517343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_919
    · exact prime_17517343
  · decide +kernel

theorem prime_2221584474649 : Nat.Prime 2221584474649 := by
  apply nodeValid_prime [2, 3, 7, 11, 191, 6294011] ⟨2221584474649, 19, [(2, 3), (3, 1), (7, 1), (11, 1), (191, 1), (6294011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_191
    · exact prime_6294011
  · decide +kernel

theorem prime_2221584499747 : Nat.Prime 2221584499747 := by
  apply nodeValid_prime [2, 3, 98317, 418447] ⟨2221584499747, 2, [(2, 1), (3, 3), (98317, 1), (418447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_98317
    · exact prime_418447
  · decide +kernel

theorem prime_2223823422017 : Nat.Prime 2223823422017 := by
  apply nodeValid_prime [2, 7, 7643, 649469] ⟨2223823422017, 3, [(2, 6), (7, 1), (7643, 1), (649469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7643
    · exact prime_649469
  · decide +kernel

theorem prime_2223823425563 : Nat.Prime 2223823425563 := by
  apply nodeValid_prime [2, 37, 66959, 448807] ⟨2223823425563, 2, [(2, 1), (37, 1), (66959, 1), (448807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_66959
    · exact prime_448807
  · decide +kernel

theorem prime_2223823426289 : Nat.Prime 2223823426289 := by
  apply nodeValid_prime [2, 23, 97, 251, 248203] ⟨2223823426289, 3, [(2, 4), (23, 1), (97, 1), (251, 1), (248203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_97
    · exact prime_251
    · exact prime_248203
  · decide +kernel

theorem prime_2226063827341 : Nat.Prime 2226063827341 := by
  apply nodeValid_prime [2, 3, 5, 17, 1109, 218657] ⟨2226063827341, 2, [(2, 2), (3, 3), (5, 1), (17, 1), (1109, 1), (218657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1109
    · exact prime_218657
  · decide +kernel

theorem prime_2226063827891 : Nat.Prime 2226063827891 := by
  apply nodeValid_prime [2, 5, 7, 43, 6833, 108233] ⟨2226063827891, 6, [(2, 1), (5, 1), (7, 1), (43, 1), (6833, 1), (108233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_6833
    · exact prime_108233
  · decide +kernel

theorem prime_2226063866381 : Nat.Prime 2226063866381 := by
  apply nodeValid_prime [2, 5, 127, 876403097] ⟨2226063866381, 2, [(2, 2), (5, 1), (127, 1), (876403097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_876403097
  · decide +kernel

theorem prime_2228305837189 : Nat.Prime 2228305837189 := by
  apply nodeValid_prime [2, 3, 185692153099] ⟨2228305837189, 6, [(2, 2), (3, 1), (185692153099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_185692153099
  · decide +kernel

theorem prime_2228305899773 : Nat.Prime 2228305899773 := by
  apply nodeValid_prime [2, 2377, 3571, 65629] ⟨2228305899773, 2, [(2, 2), (2377, 1), (3571, 1), (65629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2377
    · exact prime_3571
    · exact prime_65629
  · decide +kernel

theorem prime_2228305900217 : Nat.Prime 2228305900217 := by
  apply nodeValid_prime [2, 11, 25321657957] ⟨2228305900217, 3, [(2, 3), (11, 1), (25321657957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_25321657957
  · decide +kernel

theorem prime_2230549332203 : Nat.Prime 2230549332203 := by
  apply nodeValid_prime [2, 1115274666101] ⟨2230549332203, 2, [(2, 1), (1115274666101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1115274666101
  · decide +kernel

theorem prime_2230549358809 : Nat.Prime 2230549358809 := by
  apply nodeValid_prime [2, 3, 3643, 25511819] ⟨2230549358809, 11, [(2, 3), (3, 1), (3643, 1), (25511819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3643
    · exact prime_25511819
  · decide +kernel

theorem prime_2230549358887 : Nat.Prime 2230549358887 := by
  apply nodeValid_prime [2, 3, 29, 1489, 318863] ⟨2230549358887, 3, [(2, 1), (3, 4), (29, 1), (1489, 1), (318863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1489
    · exact prime_318863
  · decide +kernel

theorem prime_2232794343343 : Nat.Prime 2232794343343 := by
  apply nodeValid_prime [2, 3, 17, 21890140621] ⟨2232794343343, 5, [(2, 1), (3, 1), (17, 1), (21890140621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_21890140621
  · decide +kernel

theorem prime_2232794421983 : Nat.Prime 2232794421983 := by
  apply nodeValid_prime [2, 43, 25962725837] ⟨2232794421983, 5, [(2, 1), (43, 1), (25962725837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_25962725837
  · decide +kernel

theorem prime_2232794422577 : Nat.Prime 2232794422577 := by
  apply nodeValid_prime [2, 59, 6043, 391403] ⟨2232794422577, 3, [(2, 4), (59, 1), (6043, 1), (391403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_6043
    · exact prime_391403
  · decide +kernel

theorem prime_2235040871417 : Nat.Prime 2235040871417 := by
  apply nodeValid_prime [2, 277, 1008592451] ⟨2235040871417, 3, [(2, 3), (277, 1), (1008592451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_1008592451
  · decide +kernel

theorem prime_2235040872209 : Nat.Prime 2235040872209 := by
  apply nodeValid_prime [2, 23, 6073480631] ⟨2235040872209, 3, [(2, 4), (23, 1), (6073480631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_6073480631
  · decide +kernel

theorem prime_2235040881767 : Nat.Prime 2235040881767 := by
  apply nodeValid_prime [2, 7, 11, 37, 35659097] ⟨2235040881767, 5, [(2, 1), (7, 1), (11, 2), (37, 1), (35659097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_37
    · exact prime_35659097
  · decide +kernel

theorem prime_2237288948963 : Nat.Prime 2237288948963 := by
  apply nodeValid_prime [2, 79, 613, 23099603] ⟨2237288948963, 2, [(2, 1), (79, 1), (613, 1), (23099603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_613
    · exact prime_23099603
  · decide +kernel

theorem prime_2237288969351 : Nat.Prime 2237288969351 := by
  apply nodeValid_prime [2, 5, 23, 61, 257, 124097] ⟨2237288969351, 7, [(2, 1), (5, 2), (23, 1), (61, 1), (257, 1), (124097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_61
    · exact prime_257
    · exact prime_124097
  · decide +kernel

theorem prime_2237288969977 : Nat.Prime 2237288969977 := by
  apply nodeValid_prime [2, 3, 17, 79, 271, 256133] ⟨2237288969977, 5, [(2, 3), (3, 1), (17, 1), (79, 1), (271, 1), (256133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_79
    · exact prime_271
    · exact prime_256133
  · decide +kernel

theorem prime_2239538515111 : Nat.Prime 2239538515111 := by
  apply nodeValid_prime [2, 3, 5, 13, 307, 159871] ⟨2239538515111, 6, [(2, 1), (3, 3), (5, 1), (13, 2), (307, 1), (159871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_307
    · exact prime_159871
  · decide +kernel

theorem prime_2239538515237 : Nat.Prime 2239538515237 := by
  apply nodeValid_prime [2, 3, 11, 43, 131520937] ⟨2239538515237, 2, [(2, 2), (3, 2), (11, 1), (43, 1), (131520937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_131520937
  · decide +kernel

theorem prime_2239538555621 : Nat.Prime 2239538555621 := by
  apply nodeValid_prime [2, 5, 16693, 6708017] ⟨2239538555621, 3, [(2, 2), (5, 1), (16693, 1), (6708017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16693
    · exact prime_6708017
  · decide +kernel

theorem prime_2241789681259 : Nat.Prime 2241789681259 := by
  apply nodeValid_prime [2, 3, 127, 1297, 84011] ⟨2241789681259, 3, [(2, 1), (3, 4), (127, 1), (1297, 1), (84011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_1297
    · exact prime_84011
  · decide +kernel

theorem prime_2241789683173 : Nat.Prime 2241789683173 := by
  apply nodeValid_prime [2, 3, 13, 37, 59, 6582889] ⟨2241789683173, 5, [(2, 2), (3, 1), (13, 1), (37, 1), (59, 1), (6582889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_59
    · exact prime_6582889
  · decide +kernel

theorem prime_2241789699367 : Nat.Prime 2241789699367 := by
  apply nodeValid_prime [2, 3, 7, 47, 281, 443, 3041] ⟨2241789699367, 3, [(2, 1), (3, 2), (7, 1), (47, 1), (281, 1), (443, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_281
    · exact prime_443
    · exact prime_3041
  · decide +kernel

theorem prime_2244042334361 : Nat.Prime 2244042334361 := by
  apply nodeValid_prime [2, 5, 113, 127, 3909209] ⟨2244042334361, 3, [(2, 3), (5, 1), (113, 1), (127, 1), (3909209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
    · exact prime_127
    · exact prime_3909209
  · decide +kernel

theorem prime_2244042335201 : Nat.Prime 2244042335201 := by
  apply nodeValid_prime [2, 5, 47, 1279, 46663] ⟨2244042335201, 3, [(2, 5), (5, 2), (47, 1), (1279, 1), (46663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_1279
    · exact prime_46663
  · decide +kernel

theorem prime_2244042379781 : Nat.Prime 2244042379781 := by
  apply nodeValid_prime [2, 5, 53, 2117021113] ⟨2244042379781, 3, [(2, 2), (5, 1), (53, 1), (2117021113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_2117021113
  · decide +kernel

end Sude.Lucas.Generated
