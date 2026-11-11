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
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0126

/-! Generated Lucas nodes for the FT base; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7577 : Nat.Prime 7577 := by
  apply nodeValid_prime [2, 947] ⟨7577, 3, [(2, 3), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_947
  · decide +kernel

theorem prime_7753 : Nat.Prime 7753 := by
  apply nodeValid_prime [2, 3, 17, 19] ⟨7753, 10, [(2, 3), (3, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_8087 : Nat.Prime 8087 := by
  apply nodeValid_prime [2, 13, 311] ⟨8087, 5, [(2, 1), (13, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_311
  · decide +kernel

theorem prime_8231 : Nat.Prime 8231 := by
  apply nodeValid_prime [2, 5, 823] ⟨8231, 11, [(2, 1), (5, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_823
  · decide +kernel

theorem prime_8293 : Nat.Prime 8293 := by
  apply nodeValid_prime [2, 3, 691] ⟨8293, 2, [(2, 2), (3, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
  · decide +kernel

theorem prime_8629 : Nat.Prime 8629 := by
  apply nodeValid_prime [2, 3, 719] ⟨8629, 6, [(2, 2), (3, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
  · decide +kernel

theorem prime_8707 : Nat.Prime 8707 := by
  apply nodeValid_prime [2, 3, 1451] ⟨8707, 5, [(2, 1), (3, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
  · decide +kernel

theorem prime_8831 : Nat.Prime 8831 := by
  apply nodeValid_prime [2, 5, 883] ⟨8831, 7, [(2, 1), (5, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_883
  · decide +kernel

theorem prime_9001 : Nat.Prime 9001 := by
  apply nodeValid_prime [2, 3, 5] ⟨9001, 7, [(2, 3), (3, 2), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_9041 : Nat.Prime 9041 := by
  apply nodeValid_prime [2, 5, 113] ⟨9041, 3, [(2, 4), (5, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_9161 : Nat.Prime 9161 := by
  apply nodeValid_prime [2, 5, 229] ⟨9161, 3, [(2, 3), (5, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
  · decide +kernel

theorem prime_9241 : Nat.Prime 9241 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨9241, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_9277 : Nat.Prime 9277 := by
  apply nodeValid_prime [2, 3, 773] ⟨9277, 5, [(2, 2), (3, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_773
  · decide +kernel

theorem prime_9437 : Nat.Prime 9437 := by
  apply nodeValid_prime [2, 7, 337] ⟨9437, 2, [(2, 2), (7, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_337
  · decide +kernel

theorem prime_9521 : Nat.Prime 9521 := by
  apply nodeValid_prime [2, 5, 7, 17] ⟨9521, 3, [(2, 4), (5, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_9901 : Nat.Prime 9901 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨9901, 2, [(2, 2), (3, 2), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_9973 : Nat.Prime 9973 := by
  apply nodeValid_prime [2, 3, 277] ⟨9973, 11, [(2, 2), (3, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
  · decide +kernel

theorem prime_10079 : Nat.Prime 10079 := by
  apply nodeValid_prime [2, 5039] ⟨10079, 11, [(2, 1), (5039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5039
  · decide +kernel

theorem prime_10193 : Nat.Prime 10193 := by
  apply nodeValid_prime [2, 7, 13] ⟨10193, 3, [(2, 4), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_10463 : Nat.Prime 10463 := by
  apply nodeValid_prime [2, 5231] ⟨10463, 5, [(2, 1), (5231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5231
  · decide +kernel

theorem prime_10909 : Nat.Prime 10909 := by
  apply nodeValid_prime [2, 3, 101] ⟨10909, 2, [(2, 2), (3, 3), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_11621 : Nat.Prime 11621 := by
  apply nodeValid_prime [2, 5, 7, 83] ⟨11621, 2, [(2, 2), (5, 1), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_11789 : Nat.Prime 11789 := by
  apply nodeValid_prime [2, 7, 421] ⟨11789, 2, [(2, 2), (7, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_421
  · decide +kernel

theorem prime_11887 : Nat.Prime 11887 := by
  apply nodeValid_prime [2, 3, 7, 283] ⟨11887, 3, [(2, 1), (3, 1), (7, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
  · decide +kernel

theorem prime_11987 : Nat.Prime 11987 := by
  apply nodeValid_prime [2, 13, 461] ⟨11987, 2, [(2, 1), (13, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_461
  · decide +kernel

theorem prime_12037 : Nat.Prime 12037 := by
  apply nodeValid_prime [2, 3, 17, 59] ⟨12037, 5, [(2, 2), (3, 1), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_12041 : Nat.Prime 12041 := by
  apply nodeValid_prime [2, 5, 7, 43] ⟨12041, 3, [(2, 3), (5, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_12157 : Nat.Prime 12157 := by
  apply nodeValid_prime [2, 3, 1013] ⟨12157, 2, [(2, 2), (3, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1013
  · decide +kernel

theorem prime_12211 : Nat.Prime 12211 := by
  apply nodeValid_prime [2, 3, 5, 11, 37] ⟨12211, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_12277 : Nat.Prime 12277 := by
  apply nodeValid_prime [2, 3, 11, 31] ⟨12277, 2, [(2, 2), (3, 2), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_12301 : Nat.Prime 12301 := by
  apply nodeValid_prime [2, 3, 5, 41] ⟨12301, 2, [(2, 2), (3, 1), (5, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_12377 : Nat.Prime 12377 := by
  apply nodeValid_prime [2, 7, 13, 17] ⟨12377, 6, [(2, 3), (7, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_12409 : Nat.Prime 12409 := by
  apply nodeValid_prime [2, 3, 11, 47] ⟨12409, 7, [(2, 3), (3, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_12451 : Nat.Prime 12451 := by
  apply nodeValid_prime [2, 3, 5, 83] ⟨12451, 3, [(2, 1), (3, 1), (5, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
  · decide +kernel

theorem prime_12473 : Nat.Prime 12473 := by
  apply nodeValid_prime [2, 1559] ⟨12473, 3, [(2, 3), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1559
  · decide +kernel

theorem prime_12553 : Nat.Prime 12553 := by
  apply nodeValid_prime [2, 3, 523] ⟨12553, 5, [(2, 3), (3, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
  · decide +kernel

theorem prime_12697 : Nat.Prime 12697 := by
  apply nodeValid_prime [2, 3, 23] ⟨12697, 7, [(2, 3), (3, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_12739 : Nat.Prime 12739 := by
  apply nodeValid_prime [2, 3, 11, 193] ⟨12739, 2, [(2, 1), (3, 1), (11, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193
  · decide +kernel

theorem prime_12757 : Nat.Prime 12757 := by
  apply nodeValid_prime [2, 3, 1063] ⟨12757, 2, [(2, 2), (3, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1063
  · decide +kernel

theorem prime_12763 : Nat.Prime 12763 := by
  apply nodeValid_prime [2, 3, 709] ⟨12763, 2, [(2, 1), (3, 2), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_709
  · decide +kernel

theorem prime_12821 : Nat.Prime 12821 := by
  apply nodeValid_prime [2, 5, 641] ⟨12821, 2, [(2, 2), (5, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
  · decide +kernel

theorem prime_12889 : Nat.Prime 12889 := by
  apply nodeValid_prime [2, 3, 179] ⟨12889, 13, [(2, 3), (3, 2), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
  · decide +kernel

theorem prime_12983 : Nat.Prime 12983 := by
  apply nodeValid_prime [2, 6491] ⟨12983, 5, [(2, 1), (6491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6491
  · decide +kernel

theorem prime_13121 : Nat.Prime 13121 := by
  apply nodeValid_prime [2, 5, 41] ⟨13121, 7, [(2, 6), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_13151 : Nat.Prime 13151 := by
  apply nodeValid_prime [2, 5, 263] ⟨13151, 13, [(2, 1), (5, 2), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_13337 : Nat.Prime 13337 := by
  apply nodeValid_prime [2, 1667] ⟨13337, 3, [(2, 3), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1667
  · decide +kernel

theorem prime_13523 : Nat.Prime 13523 := by
  apply nodeValid_prime [2, 6761] ⟨13523, 2, [(2, 1), (6761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6761
  · decide +kernel

theorem prime_13633 : Nat.Prime 13633 := by
  apply nodeValid_prime [2, 3, 71] ⟨13633, 5, [(2, 6), (3, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_13669 : Nat.Prime 13669 := by
  apply nodeValid_prime [2, 3, 17, 67] ⟨13669, 6, [(2, 2), (3, 1), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_13697 : Nat.Prime 13697 := by
  apply nodeValid_prime [2, 107] ⟨13697, 3, [(2, 7), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_107
  · decide +kernel

theorem prime_13807 : Nat.Prime 13807 := by
  apply nodeValid_prime [2, 3, 13, 59] ⟨13807, 5, [(2, 1), (3, 2), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_13829 : Nat.Prime 13829 := by
  apply nodeValid_prime [2, 3457] ⟨13829, 2, [(2, 2), (3457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3457
  · decide +kernel

theorem prime_13831 : Nat.Prime 13831 := by
  apply nodeValid_prime [2, 3, 5, 461] ⟨13831, 6, [(2, 1), (3, 1), (5, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_461
  · decide +kernel

theorem prime_13997 : Nat.Prime 13997 := by
  apply nodeValid_prime [2, 3499] ⟨13997, 2, [(2, 2), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3499
  · decide +kernel

theorem prime_14051 : Nat.Prime 14051 := by
  apply nodeValid_prime [2, 5, 281] ⟨14051, 2, [(2, 1), (5, 2), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_281
  · decide +kernel

theorem prime_14107 : Nat.Prime 14107 := by
  apply nodeValid_prime [2, 3, 2351] ⟨14107, 2, [(2, 1), (3, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2351
  · decide +kernel

theorem prime_14207 : Nat.Prime 14207 := by
  apply nodeValid_prime [2, 7103] ⟨14207, 5, [(2, 1), (7103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7103
  · decide +kernel

theorem prime_14401 : Nat.Prime 14401 := by
  apply nodeValid_prime [2, 3, 5] ⟨14401, 11, [(2, 6), (3, 2), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_14407 : Nat.Prime 14407 := by
  apply nodeValid_prime [2, 3, 7] ⟨14407, 19, [(2, 1), (3, 1), (7, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_14489 : Nat.Prime 14489 := by
  apply nodeValid_prime [2, 1811] ⟨14489, 3, [(2, 3), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1811
  · decide +kernel

theorem prime_14533 : Nat.Prime 14533 := by
  apply nodeValid_prime [2, 3, 7, 173] ⟨14533, 2, [(2, 2), (3, 1), (7, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173
  · decide +kernel

theorem prime_14563 : Nat.Prime 14563 := by
  apply nodeValid_prime [2, 3, 809] ⟨14563, 3, [(2, 1), (3, 2), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_809
  · decide +kernel

theorem prime_14591 : Nat.Prime 14591 := by
  apply nodeValid_prime [2, 5, 1459] ⟨14591, 11, [(2, 1), (5, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1459
  · decide +kernel

theorem prime_14627 : Nat.Prime 14627 := by
  apply nodeValid_prime [2, 71, 103] ⟨14627, 2, [(2, 1), (71, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_103
  · decide +kernel

theorem prime_14713 : Nat.Prime 14713 := by
  apply nodeValid_prime [2, 3, 613] ⟨14713, 5, [(2, 3), (3, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
  · decide +kernel

theorem prime_14843 : Nat.Prime 14843 := by
  apply nodeValid_prime [2, 41, 181] ⟨14843, 2, [(2, 1), (41, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_181
  · decide +kernel

theorem prime_14923 : Nat.Prime 14923 := by
  apply nodeValid_prime [2, 3, 829] ⟨14923, 2, [(2, 1), (3, 2), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_829
  · decide +kernel

theorem prime_14947 : Nat.Prime 14947 := by
  apply nodeValid_prime [2, 3, 47, 53] ⟨14947, 2, [(2, 1), (3, 1), (47, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_53
  · decide +kernel

theorem prime_15083 : Nat.Prime 15083 := by
  apply nodeValid_prime [2, 7541] ⟨15083, 2, [(2, 1), (7541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7541
  · decide +kernel

theorem prime_15187 : Nat.Prime 15187 := by
  apply nodeValid_prime [2, 3, 2531] ⟨15187, 2, [(2, 1), (3, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2531
  · decide +kernel

theorem prime_15193 : Nat.Prime 15193 := by
  apply nodeValid_prime [2, 3, 211] ⟨15193, 5, [(2, 3), (3, 2), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
  · decide +kernel

theorem prime_15263 : Nat.Prime 15263 := by
  apply nodeValid_prime [2, 13, 587] ⟨15263, 5, [(2, 1), (13, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_587
  · decide +kernel

theorem prime_15299 : Nat.Prime 15299 := by
  apply nodeValid_prime [2, 7649] ⟨15299, 2, [(2, 1), (7649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7649
  · decide +kernel

theorem prime_15439 : Nat.Prime 15439 := by
  apply nodeValid_prime [2, 3, 31, 83] ⟨15439, 3, [(2, 1), (3, 1), (31, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_83
  · decide +kernel

theorem prime_15527 : Nat.Prime 15527 := by
  apply nodeValid_prime [2, 7, 1109] ⟨15527, 5, [(2, 1), (7, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1109
  · decide +kernel

theorem prime_15541 : Nat.Prime 15541 := by
  apply nodeValid_prime [2, 3, 5, 7, 37] ⟨15541, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_15569 : Nat.Prime 15569 := by
  apply nodeValid_prime [2, 7, 139] ⟨15569, 3, [(2, 4), (7, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_15583 : Nat.Prime 15583 := by
  apply nodeValid_prime [2, 3, 7, 53] ⟨15583, 5, [(2, 1), (3, 1), (7, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_15607 : Nat.Prime 15607 := by
  apply nodeValid_prime [2, 3, 17] ⟨15607, 3, [(2, 1), (3, 3), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_15649 : Nat.Prime 15649 := by
  apply nodeValid_prime [2, 3, 163] ⟨15649, 11, [(2, 5), (3, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
  · decide +kernel

theorem prime_15761 : Nat.Prime 15761 := by
  apply nodeValid_prime [2, 5, 197] ⟨15761, 3, [(2, 4), (5, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
  · decide +kernel

theorem prime_15823 : Nat.Prime 15823 := by
  apply nodeValid_prime [2, 3, 293] ⟨15823, 3, [(2, 1), (3, 3), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
  · decide +kernel

theorem prime_15859 : Nat.Prime 15859 := by
  apply nodeValid_prime [2, 3, 881] ⟨15859, 2, [(2, 1), (3, 2), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_881
  · decide +kernel

theorem prime_15877 : Nat.Prime 15877 := by
  apply nodeValid_prime [2, 3, 7] ⟨15877, 5, [(2, 2), (3, 4), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_15889 : Nat.Prime 15889 := by
  apply nodeValid_prime [2, 3, 331] ⟨15889, 21, [(2, 4), (3, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
  · decide +kernel

theorem prime_15923 : Nat.Prime 15923 := by
  apply nodeValid_prime [2, 19, 419] ⟨15923, 2, [(2, 1), (19, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_419
  · decide +kernel

theorem prime_16057 : Nat.Prime 16057 := by
  apply nodeValid_prime [2, 3, 223] ⟨16057, 7, [(2, 3), (3, 2), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
  · decide +kernel

theorem prime_16061 : Nat.Prime 16061 := by
  apply nodeValid_prime [2, 5, 11, 73] ⟨16061, 12, [(2, 2), (5, 1), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_16103 : Nat.Prime 16103 := by
  apply nodeValid_prime [2, 83, 97] ⟨16103, 5, [(2, 1), (83, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_97
  · decide +kernel

theorem prime_16141 : Nat.Prime 16141 := by
  apply nodeValid_prime [2, 3, 5, 269] ⟨16141, 6, [(2, 2), (3, 1), (5, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_269
  · decide +kernel

theorem prime_16217 : Nat.Prime 16217 := by
  apply nodeValid_prime [2, 2027] ⟨16217, 3, [(2, 3), (2027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2027
  · decide +kernel

theorem prime_16273 : Nat.Prime 16273 := by
  apply nodeValid_prime [2, 3, 113] ⟨16273, 7, [(2, 4), (3, 2), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
  · decide +kernel

theorem prime_16301 : Nat.Prime 16301 := by
  apply nodeValid_prime [2, 5, 163] ⟨16301, 2, [(2, 2), (5, 2), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
  · decide +kernel

theorem prime_16349 : Nat.Prime 16349 := by
  apply nodeValid_prime [2, 61, 67] ⟨16349, 2, [(2, 2), (61, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_67
  · decide +kernel

theorem prime_16381 : Nat.Prime 16381 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨16381, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_16447 : Nat.Prime 16447 := by
  apply nodeValid_prime [2, 3, 2741] ⟨16447, 3, [(2, 1), (3, 1), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2741
  · decide +kernel

theorem prime_16451 : Nat.Prime 16451 := by
  apply nodeValid_prime [2, 5, 7, 47] ⟨16451, 7, [(2, 1), (5, 2), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_16487 : Nat.Prime 16487 := by
  apply nodeValid_prime [2, 8243] ⟨16487, 5, [(2, 1), (8243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8243
  · decide +kernel

theorem prime_16529 : Nat.Prime 16529 := by
  apply nodeValid_prime [2, 1033] ⟨16529, 3, [(2, 4), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1033
  · decide +kernel

theorem prime_16547 : Nat.Prime 16547 := by
  apply nodeValid_prime [2, 8273] ⟨16547, 2, [(2, 1), (8273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8273
  · decide +kernel

theorem prime_16787 : Nat.Prime 16787 := by
  apply nodeValid_prime [2, 7, 11, 109] ⟨16787, 2, [(2, 1), (7, 1), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_16883 : Nat.Prime 16883 := by
  apply nodeValid_prime [2, 23, 367] ⟨16883, 2, [(2, 1), (23, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_367
  · decide +kernel

theorem prime_16889 : Nat.Prime 16889 := by
  apply nodeValid_prime [2, 2111] ⟨16889, 3, [(2, 3), (2111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2111
  · decide +kernel

theorem prime_16943 : Nat.Prime 16943 := by
  apply nodeValid_prime [2, 43, 197] ⟨16943, 5, [(2, 1), (43, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_197
  · decide +kernel

theorem prime_16987 : Nat.Prime 16987 := by
  apply nodeValid_prime [2, 3, 19, 149] ⟨16987, 3, [(2, 1), (3, 1), (19, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_149
  · decide +kernel

theorem prime_17021 : Nat.Prime 17021 := by
  apply nodeValid_prime [2, 5, 23, 37] ⟨17021, 2, [(2, 2), (5, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_17027 : Nat.Prime 17027 := by
  apply nodeValid_prime [2, 8513] ⟨17027, 2, [(2, 1), (8513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8513
  · decide +kernel

theorem prime_17053 : Nat.Prime 17053 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨17053, 2, [(2, 2), (3, 1), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_17123 : Nat.Prime 17123 := by
  apply nodeValid_prime [2, 7, 1223] ⟨17123, 2, [(2, 1), (7, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1223
  · decide +kernel

theorem prime_17183 : Nat.Prime 17183 := by
  apply nodeValid_prime [2, 11, 71] ⟨17183, 5, [(2, 1), (11, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_17321 : Nat.Prime 17321 := by
  apply nodeValid_prime [2, 5, 433] ⟨17321, 3, [(2, 3), (5, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_433
  · decide +kernel

theorem prime_17417 : Nat.Prime 17417 := by
  apply nodeValid_prime [2, 7, 311] ⟨17417, 3, [(2, 3), (7, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_311
  · decide +kernel

theorem prime_17489 : Nat.Prime 17489 := by
  apply nodeValid_prime [2, 1093] ⟨17489, 3, [(2, 4), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1093
  · decide +kernel

theorem prime_17491 : Nat.Prime 17491 := by
  apply nodeValid_prime [2, 3, 5, 11, 53] ⟨17491, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_17509 : Nat.Prime 17509 := by
  apply nodeValid_prime [2, 3, 1459] ⟨17509, 2, [(2, 2), (3, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1459
  · decide +kernel

theorem prime_17539 : Nat.Prime 17539 := by
  apply nodeValid_prime [2, 3, 37, 79] ⟨17539, 3, [(2, 1), (3, 1), (37, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_79
  · decide +kernel

theorem prime_17609 : Nat.Prime 17609 := by
  apply nodeValid_prime [2, 31, 71] ⟨17609, 3, [(2, 3), (31, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_71
  · decide +kernel

theorem prime_17623 : Nat.Prime 17623 := by
  apply nodeValid_prime [2, 3, 11, 89] ⟨17623, 3, [(2, 1), (3, 2), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_17761 : Nat.Prime 17761 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨17761, 19, [(2, 5), (3, 1), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_17789 : Nat.Prime 17789 := by
  apply nodeValid_prime [2, 4447] ⟨17789, 2, [(2, 2), (4447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4447
  · decide +kernel

theorem prime_17837 : Nat.Prime 17837 := by
  apply nodeValid_prime [2, 7, 13] ⟨17837, 2, [(2, 2), (7, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_17911 : Nat.Prime 17911 := by
  apply nodeValid_prime [2, 3, 5, 199] ⟨17911, 3, [(2, 1), (3, 2), (5, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
  · decide +kernel

theorem prime_17921 : Nat.Prime 17921 := by
  apply nodeValid_prime [2, 5, 7] ⟨17921, 3, [(2, 9), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_17957 : Nat.Prime 17957 := by
  apply nodeValid_prime [2, 67] ⟨17957, 2, [(2, 2), (67, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67
  · decide +kernel

theorem prime_17971 : Nat.Prime 17971 := by
  apply nodeValid_prime [2, 3, 5, 599] ⟨17971, 3, [(2, 1), (3, 1), (5, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_599
  · decide +kernel

theorem prime_18047 : Nat.Prime 18047 := by
  apply nodeValid_prime [2, 7, 1289] ⟨18047, 5, [(2, 1), (7, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1289
  · decide +kernel

theorem prime_18049 : Nat.Prime 18049 := by
  apply nodeValid_prime [2, 3, 47] ⟨18049, 13, [(2, 7), (3, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_18119 : Nat.Prime 18119 := by
  apply nodeValid_prime [2, 9059] ⟨18119, 17, [(2, 1), (9059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9059
  · decide +kernel

theorem prime_18143 : Nat.Prime 18143 := by
  apply nodeValid_prime [2, 47, 193] ⟨18143, 5, [(2, 1), (47, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_193
  · decide +kernel

theorem prime_18169 : Nat.Prime 18169 := by
  apply nodeValid_prime [2, 3, 757] ⟨18169, 11, [(2, 3), (3, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_757
  · decide +kernel

theorem prime_18233 : Nat.Prime 18233 := by
  apply nodeValid_prime [2, 43, 53] ⟨18233, 3, [(2, 3), (43, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_53
  · decide +kernel

theorem prime_18329 : Nat.Prime 18329 := by
  apply nodeValid_prime [2, 29, 79] ⟨18329, 3, [(2, 3), (29, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_79
  · decide +kernel

theorem prime_18371 : Nat.Prime 18371 := by
  apply nodeValid_prime [2, 5, 11, 167] ⟨18371, 11, [(2, 1), (5, 1), (11, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_167
  · decide +kernel

theorem prime_18397 : Nat.Prime 18397 := by
  apply nodeValid_prime [2, 3, 7, 73] ⟨18397, 6, [(2, 2), (3, 2), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_18413 : Nat.Prime 18413 := by
  apply nodeValid_prime [2, 4603] ⟨18413, 2, [(2, 2), (4603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4603
  · decide +kernel

theorem prime_18539 : Nat.Prime 18539 := by
  apply nodeValid_prime [2, 13, 23, 31] ⟨18539, 6, [(2, 1), (13, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_18541 : Nat.Prime 18541 := by
  apply nodeValid_prime [2, 3, 5, 103] ⟨18541, 6, [(2, 2), (3, 2), (5, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_18637 : Nat.Prime 18637 := by
  apply nodeValid_prime [2, 3, 1553] ⟨18637, 2, [(2, 2), (3, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1553
  · decide +kernel

theorem prime_18671 : Nat.Prime 18671 := by
  apply nodeValid_prime [2, 5, 1867] ⟨18671, 7, [(2, 1), (5, 1), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1867
  · decide +kernel

theorem prime_18679 : Nat.Prime 18679 := by
  apply nodeValid_prime [2, 3, 11, 283] ⟨18679, 6, [(2, 1), (3, 1), (11, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_283
  · decide +kernel

theorem prime_18743 : Nat.Prime 18743 := by
  apply nodeValid_prime [2, 9371] ⟨18743, 5, [(2, 1), (9371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9371
  · decide +kernel

theorem prime_18797 : Nat.Prime 18797 := by
  apply nodeValid_prime [2, 37, 127] ⟨18797, 3, [(2, 2), (37, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_127
  · decide +kernel

theorem prime_18839 : Nat.Prime 18839 := by
  apply nodeValid_prime [2, 9419] ⟨18839, 7, [(2, 1), (9419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9419
  · decide +kernel

theorem prime_18869 : Nat.Prime 18869 := by
  apply nodeValid_prime [2, 53, 89] ⟨18869, 2, [(2, 2), (53, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_89
  · decide +kernel

theorem prime_18913 : Nat.Prime 18913 := by
  apply nodeValid_prime [2, 3, 197] ⟨18913, 7, [(2, 5), (3, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
  · decide +kernel

theorem prime_18919 : Nat.Prime 18919 := by
  apply nodeValid_prime [2, 3, 1051] ⟨18919, 3, [(2, 1), (3, 2), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1051
  · decide +kernel

theorem prime_18959 : Nat.Prime 18959 := by
  apply nodeValid_prime [2, 9479] ⟨18959, 13, [(2, 1), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9479
  · decide +kernel

theorem prime_18973 : Nat.Prime 18973 := by
  apply nodeValid_prime [2, 3, 17, 31] ⟨18973, 2, [(2, 2), (3, 2), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_19013 : Nat.Prime 19013 := by
  apply nodeValid_prime [2, 7, 97] ⟨19013, 2, [(2, 2), (7, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_97
  · decide +kernel

theorem prime_19087 : Nat.Prime 19087 := by
  apply nodeValid_prime [2, 3, 3181] ⟨19087, 19, [(2, 1), (3, 1), (3181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3181
  · decide +kernel

end Sude.Lucas.Generated
