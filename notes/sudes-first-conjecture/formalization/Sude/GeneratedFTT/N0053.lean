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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5981 : Nat.Prime 5981 := by
  apply nodeValid_prime [2, 5, 13, 23] ⟨5981, 3, [(2, 2), (5, 1), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_6277 : Nat.Prime 6277 := by
  apply nodeValid_prime [2, 3, 523] ⟨6277, 2, [(2, 2), (3, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
  · decide +kernel

theorem prime_10663 : Nat.Prime 10663 := by
  apply nodeValid_prime [2, 3, 1777] ⟨10663, 3, [(2, 1), (3, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1777
  · decide +kernel

theorem prime_12343 : Nat.Prime 12343 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨12343, 7, [(2, 1), (3, 1), (11, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_13487 : Nat.Prime 13487 := by
  apply nodeValid_prime [2, 11, 613] ⟨13487, 5, [(2, 1), (11, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_613
  · decide +kernel

theorem prime_13597 : Nat.Prime 13597 := by
  apply nodeValid_prime [2, 3, 11, 103] ⟨13597, 5, [(2, 2), (3, 1), (11, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_103
  · decide +kernel

theorem prime_13751 : Nat.Prime 13751 := by
  apply nodeValid_prime [2, 5, 11] ⟨13751, 11, [(2, 1), (5, 4), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_14149 : Nat.Prime 14149 := by
  apply nodeValid_prime [2, 3, 131] ⟨14149, 6, [(2, 2), (3, 3), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_16553 : Nat.Prime 16553 := by
  apply nodeValid_prime [2, 2069] ⟨16553, 3, [(2, 3), (2069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2069
  · decide +kernel

theorem prime_17137 : Nat.Prime 17137 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨17137, 5, [(2, 4), (3, 2), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_23011 : Nat.Prime 23011 := by
  apply nodeValid_prime [2, 3, 5, 13, 59] ⟨23011, 7, [(2, 1), (3, 1), (5, 1), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_24571 : Nat.Prime 24571 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨24571, 7, [(2, 1), (3, 3), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_25147 : Nat.Prime 25147 := by
  apply nodeValid_prime [2, 3, 11, 127] ⟨25147, 2, [(2, 1), (3, 2), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_44087 : Nat.Prime 44087 := by
  apply nodeValid_prime [2, 7, 47, 67] ⟨44087, 5, [(2, 1), (7, 1), (47, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_67
  · decide +kernel

theorem prime_65293 : Nat.Prime 65293 := by
  apply nodeValid_prime [2, 3, 5441] ⟨65293, 2, [(2, 2), (3, 1), (5441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5441
  · decide +kernel

theorem prime_67679 : Nat.Prime 67679 := by
  apply nodeValid_prime [2, 13, 19, 137] ⟨67679, 19, [(2, 1), (13, 1), (19, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_75347 : Nat.Prime 75347 := by
  apply nodeValid_prime [2, 101, 373] ⟨75347, 2, [(2, 1), (101, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_373
  · decide +kernel

theorem prime_75689 : Nat.Prime 75689 := by
  apply nodeValid_prime [2, 9461] ⟨75689, 3, [(2, 3), (9461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9461
  · decide +kernel

theorem prime_80611 : Nat.Prime 80611 := by
  apply nodeValid_prime [2, 3, 5, 2687] ⟨80611, 2, [(2, 1), (3, 1), (5, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2687
  · decide +kernel

theorem prime_80923 : Nat.Prime 80923 := by
  apply nodeValid_prime [2, 3, 13487] ⟨80923, 2, [(2, 1), (3, 1), (13487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13487
  · decide +kernel

theorem prime_85259 : Nat.Prime 85259 := by
  apply nodeValid_prime [2, 47, 907] ⟨85259, 2, [(2, 1), (47, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_907
  · decide +kernel

theorem prime_101359 : Nat.Prime 101359 := by
  apply nodeValid_prime [2, 3, 1877] ⟨101359, 3, [(2, 1), (3, 3), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1877
  · decide +kernel

theorem prime_120623 : Nat.Prime 120623 := by
  apply nodeValid_prime [2, 41, 1471] ⟨120623, 5, [(2, 1), (41, 1), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1471
  · decide +kernel

theorem prime_124771 : Nat.Prime 124771 := by
  apply nodeValid_prime [2, 3, 5, 4159] ⟨124771, 10, [(2, 1), (3, 1), (5, 1), (4159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4159
  · decide +kernel

theorem prime_129001 : Nat.Prime 129001 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨129001, 7, [(2, 3), (3, 1), (5, 3), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_152083 : Nat.Prime 152083 := by
  apply nodeValid_prime [2, 3, 7, 17, 71] ⟨152083, 3, [(2, 1), (3, 2), (7, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_153749 : Nat.Prime 153749 := by
  apply nodeValid_prime [2, 7, 17, 19] ⟨153749, 10, [(2, 2), (7, 1), (17, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_157081 : Nat.Prime 157081 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 17] ⟨157081, 26, [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_157483 : Nat.Prime 157483 := by
  apply nodeValid_prime [2, 3, 13, 673] ⟨157483, 2, [(2, 1), (3, 2), (13, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_673
  · decide +kernel

theorem prime_158647 : Nat.Prime 158647 := by
  apply nodeValid_prime [2, 3, 137, 193] ⟨158647, 5, [(2, 1), (3, 1), (137, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_193
  · decide +kernel

theorem prime_187277 : Nat.Prime 187277 := by
  apply nodeValid_prime [2, 46819] ⟨187277, 2, [(2, 2), (46819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46819
  · decide +kernel

theorem prime_188291 : Nat.Prime 188291 := by
  apply nodeValid_prime [2, 5, 19, 991] ⟨188291, 2, [(2, 1), (5, 1), (19, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_991
  · decide +kernel

theorem prime_188311 : Nat.Prime 188311 := by
  apply nodeValid_prime [2, 3, 5, 6277] ⟨188311, 3, [(2, 1), (3, 1), (5, 1), (6277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6277
  · decide +kernel

theorem prime_203117 : Nat.Prime 203117 := by
  apply nodeValid_prime [2, 17, 29, 103] ⟨203117, 2, [(2, 2), (17, 1), (29, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_103
  · decide +kernel

theorem prime_207721 : Nat.Prime 207721 := by
  apply nodeValid_prime [2, 3, 5, 577] ⟨207721, 7, [(2, 3), (3, 2), (5, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_577
  · decide +kernel

theorem prime_220879 : Nat.Prime 220879 := by
  apply nodeValid_prime [2, 3, 7, 1753] ⟨220879, 7, [(2, 1), (3, 2), (7, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1753
  · decide +kernel

theorem prime_244747 : Nat.Prime 244747 := by
  apply nodeValid_prime [2, 3, 13597] ⟨244747, 14, [(2, 1), (3, 2), (13597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13597
  · decide +kernel

theorem prime_282427 : Nat.Prime 282427 := by
  apply nodeValid_prime [2, 3, 103, 457] ⟨282427, 3, [(2, 1), (3, 1), (103, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_457
  · decide +kernel

theorem prime_284593 : Nat.Prime 284593 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨284593, 5, [(2, 4), (3, 1), (7, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_288283 : Nat.Prime 288283 := by
  apply nodeValid_prime [2, 3, 23, 2089] ⟨288283, 3, [(2, 1), (3, 1), (23, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2089
  · decide +kernel

theorem prime_308467 : Nat.Prime 308467 := by
  apply nodeValid_prime [2, 3, 17137] ⟨308467, 2, [(2, 1), (3, 2), (17137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17137
  · decide +kernel

theorem prime_316373 : Nat.Prime 316373 := by
  apply nodeValid_prime [2, 7, 11299] ⟨316373, 2, [(2, 2), (7, 1), (11299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11299
  · decide +kernel

theorem prime_344791 : Nat.Prime 344791 := by
  apply nodeValid_prime [2, 3, 5, 1277] ⟨344791, 3, [(2, 1), (3, 3), (5, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1277
  · decide +kernel

theorem prime_393137 : Nat.Prime 393137 := by
  apply nodeValid_prime [2, 24571] ⟨393137, 3, [(2, 4), (24571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24571
  · decide +kernel

theorem prime_429907 : Nat.Prime 429907 := by
  apply nodeValid_prime [2, 3, 137, 523] ⟨429907, 2, [(2, 1), (3, 1), (137, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_523
  · decide +kernel

theorem prime_443041 : Nat.Prime 443041 := by
  apply nodeValid_prime [2, 3, 5, 13, 71] ⟨443041, 19, [(2, 5), (3, 1), (5, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_450617 : Nat.Prime 450617 := by
  apply nodeValid_prime [2, 23, 31, 79] ⟨450617, 3, [(2, 3), (23, 1), (31, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
    · exact prime_79
  · decide +kernel

theorem prime_573047 : Nat.Prime 573047 := by
  apply nodeValid_prime [2, 181, 1583] ⟨573047, 5, [(2, 1), (181, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_1583
  · decide +kernel

theorem prime_584033 : Nat.Prime 584033 := by
  apply nodeValid_prime [2, 18251] ⟨584033, 3, [(2, 5), (18251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18251
  · decide +kernel

theorem prime_634367 : Nat.Prime 634367 := by
  apply nodeValid_prime [2, 419, 757] ⟨634367, 5, [(2, 1), (419, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_757
  · decide +kernel

theorem prime_652931 : Nat.Prime 652931 := by
  apply nodeValid_prime [2, 5, 65293] ⟨652931, 2, [(2, 1), (5, 1), (65293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_65293
  · decide +kernel

theorem prime_660097 : Nat.Prime 660097 := by
  apply nodeValid_prime [2, 3, 191] ⟨660097, 35, [(2, 7), (3, 3), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
  · decide +kernel

theorem prime_820643 : Nat.Prime 820643 := by
  apply nodeValid_prime [2, 29, 14149] ⟨820643, 2, [(2, 1), (29, 1), (14149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_14149
  · decide +kernel

theorem prime_942301 : Nat.Prime 942301 := by
  apply nodeValid_prime [2, 3, 5, 349] ⟨942301, 2, [(2, 2), (3, 3), (5, 2), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_981601 : Nat.Prime 981601 := by
  apply nodeValid_prime [2, 3, 5, 409] ⟨981601, 7, [(2, 5), (3, 1), (5, 2), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_409
  · decide +kernel

theorem prime_995447 : Nat.Prime 995447 := by
  apply nodeValid_prime [2, 53, 9391] ⟨995447, 5, [(2, 1), (53, 1), (9391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_9391
  · decide +kernel

theorem prime_1130281 : Nat.Prime 1130281 := by
  apply nodeValid_prime [2, 3, 5, 9419] ⟨1130281, 14, [(2, 3), (3, 1), (5, 1), (9419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9419
  · decide +kernel

theorem prime_1345787 : Nat.Prime 1345787 := by
  apply nodeValid_prime [2, 13, 191, 271] ⟨1345787, 2, [(2, 1), (13, 1), (191, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_191
    · exact prime_271
  · decide +kernel

theorem prime_1742989 : Nat.Prime 1742989 := by
  apply nodeValid_prime [2, 3, 13, 11173] ⟨1742989, 2, [(2, 2), (3, 1), (13, 1), (11173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_11173
  · decide +kernel

theorem prime_1850803 : Nat.Prime 1850803 := by
  apply nodeValid_prime [2, 3, 308467] ⟨1850803, 2, [(2, 1), (3, 1), (308467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_308467
  · decide +kernel

theorem prime_2623259 : Nat.Prime 2623259 := by
  apply nodeValid_prime [2, 11, 43, 47, 59] ⟨2623259, 2, [(2, 1), (11, 1), (43, 1), (47, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_47
    · exact prime_59
  · decide +kernel

theorem prime_3917587 : Nat.Prime 3917587 := by
  apply nodeValid_prime [2, 3, 652931] ⟨3917587, 2, [(2, 1), (3, 1), (652931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_652931
  · decide +kernel

theorem prime_4092433 : Nat.Prime 4092433 := by
  apply nodeValid_prime [2, 3, 85259] ⟨4092433, 5, [(2, 4), (3, 1), (85259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_85259
  · decide +kernel

theorem prime_4306231 : Nat.Prime 4306231 := by
  apply nodeValid_prime [2, 3, 5, 41, 389] ⟨4306231, 13, [(2, 1), (3, 3), (5, 1), (41, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_389
  · decide +kernel

theorem prime_4771873 : Nat.Prime 4771873 := by
  apply nodeValid_prime [2, 3, 7, 263] ⟨4771873, 5, [(2, 5), (3, 4), (7, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_263
  · decide +kernel

theorem prime_6154597 : Nat.Prime 6154597 := by
  apply nodeValid_prime [2, 3, 7, 1163] ⟨6154597, 5, [(2, 2), (3, 3), (7, 2), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1163
  · decide +kernel

theorem prime_6576863 : Nat.Prime 6576863 := by
  apply nodeValid_prime [2, 73, 107, 421] ⟨6576863, 5, [(2, 1), (73, 1), (107, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_107
    · exact prime_421
  · decide +kernel

theorem prime_6666241 : Nat.Prime 6666241 := by
  apply nodeValid_prime [2, 3, 5, 7, 31] ⟨6666241, 19, [(2, 11), (3, 1), (5, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_6732529 : Nat.Prime 6732529 := by
  apply nodeValid_prime [2, 3, 11, 41, 311] ⟨6732529, 7, [(2, 4), (3, 1), (11, 1), (41, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_311
  · decide +kernel

theorem prime_8453113 : Nat.Prime 8453113 := by
  apply nodeValid_prime [2, 3, 43, 8191] ⟨8453113, 5, [(2, 3), (3, 1), (43, 1), (8191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_8191
  · decide +kernel

theorem prime_12413579 : Nat.Prime 12413579 := by
  apply nodeValid_prime [2, 31, 347, 577] ⟨12413579, 2, [(2, 1), (31, 1), (347, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_347
    · exact prime_577
  · decide +kernel

theorem prime_12823751 : Nat.Prime 12823751 := by
  apply nodeValid_prime [2, 5, 10259] ⟨12823751, 13, [(2, 1), (5, 4), (10259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10259
  · decide +kernel

theorem prime_15401797 : Nat.Prime 15401797 := by
  apply nodeValid_prime [2, 3, 17, 103, 733] ⟨15401797, 2, [(2, 2), (3, 1), (17, 1), (103, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_103
    · exact prime_733
  · decide +kernel

theorem prime_16260269 : Nat.Prime 16260269 := by
  apply nodeValid_prime [2, 223, 18229] ⟨16260269, 2, [(2, 2), (223, 1), (18229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_18229
  · decide +kernel

theorem prime_17047031 : Nat.Prime 17047031 := by
  apply nodeValid_prime [2, 5, 7, 11, 13, 131] ⟨17047031, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (13, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_131
  · decide +kernel

theorem prime_18343393 : Nat.Prime 18343393 := by
  apply nodeValid_prime [2, 3, 109, 1753] ⟨18343393, 5, [(2, 5), (3, 1), (109, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1753
  · decide +kernel

theorem prime_25643161 : Nat.Prime 25643161 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 163] ⟨25643161, 13, [(2, 3), (3, 2), (5, 1), (19, 1), (23, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_163
  · decide +kernel

theorem prime_27846961 : Nat.Prime 27846961 := by
  apply nodeValid_prime [2, 3, 5, 29, 4001] ⟨27846961, 19, [(2, 4), (3, 1), (5, 1), (29, 1), (4001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_4001
  · decide +kernel

theorem prime_33812453 : Nat.Prime 33812453 := by
  apply nodeValid_prime [2, 8453113] ⟨33812453, 2, [(2, 2), (8453113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8453113
  · decide +kernel

theorem prime_34329037 : Nat.Prime 34329037 := by
  apply nodeValid_prime [2, 3, 7, 349, 1171] ⟨34329037, 2, [(2, 2), (3, 1), (7, 1), (349, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_349
    · exact prime_1171
  · decide +kernel

theorem prime_36558461 : Nat.Prime 36558461 := by
  apply nodeValid_prime [2, 5, 277, 6599] ⟨36558461, 2, [(2, 2), (5, 1), (277, 1), (6599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_277
    · exact prime_6599
  · decide +kernel

theorem prime_47554417 : Nat.Prime 47554417 := by
  apply nodeValid_prime [2, 3, 7, 13, 19, 191] ⟨47554417, 10, [(2, 4), (3, 2), (7, 1), (13, 1), (19, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_191
  · decide +kernel

theorem prime_57570967 : Nat.Prime 57570967 := by
  apply nodeValid_prime [2, 3, 109, 9781] ⟨57570967, 5, [(2, 1), (3, 3), (109, 1), (9781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_9781
  · decide +kernel

theorem prime_62681393 : Nat.Prime 62681393 := by
  apply nodeValid_prime [2, 3917587] ⟨62681393, 3, [(2, 4), (3917587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3917587
  · decide +kernel

theorem prime_74292143 : Nat.Prime 74292143 := by
  apply nodeValid_prime [2, 17, 29, 75347] ⟨74292143, 5, [(2, 1), (17, 1), (29, 1), (75347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_75347
  · decide +kernel

theorem prime_77512159 : Nat.Prime 77512159 := by
  apply nodeValid_prime [2, 3, 4306231] ⟨77512159, 3, [(2, 1), (3, 2), (4306231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4306231
  · decide +kernel

theorem prime_83617549 : Nat.Prime 83617549 := by
  apply nodeValid_prime [2, 3, 7, 995447] ⟨83617549, 2, [(2, 2), (3, 1), (7, 1), (995447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_995447
  · decide +kernel

theorem prime_124122851 : Nat.Prime 124122851 := by
  apply nodeValid_prime [2, 5, 263, 9439] ⟨124122851, 2, [(2, 1), (5, 2), (263, 1), (9439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
    · exact prime_9439
  · decide +kernel

theorem prime_190217669 : Nat.Prime 190217669 := by
  apply nodeValid_prime [2, 47554417] ⟨190217669, 2, [(2, 2), (47554417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_47554417
  · decide +kernel

theorem prime_195673183 : Nat.Prime 195673183 := by
  apply nodeValid_prime [2, 3, 157, 207721] ⟨195673183, 3, [(2, 1), (3, 1), (157, 1), (207721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_207721
  · decide +kernel

theorem prime_214379383 : Nat.Prime 214379383 := by
  apply nodeValid_prime [2, 3, 7, 53, 193, 499] ⟨214379383, 3, [(2, 1), (3, 1), (7, 1), (53, 1), (193, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_193
    · exact prime_499
  · decide +kernel

theorem prime_214493693 : Nat.Prime 214493693 := by
  apply nodeValid_prime [2, 7, 17, 450617] ⟨214493693, 2, [(2, 2), (7, 1), (17, 1), (450617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_450617
  · decide +kernel

theorem prime_230283869 : Nat.Prime 230283869 := by
  apply nodeValid_prime [2, 57570967] ⟨230283869, 2, [(2, 2), (57570967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57570967
  · decide +kernel

theorem prime_362009743 : Nat.Prime 362009743 := by
  apply nodeValid_prime [2, 3, 23, 2623259] ⟨362009743, 3, [(2, 1), (3, 1), (23, 1), (2623259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2623259
  · decide +kernel

theorem prime_375512309 : Nat.Prime 375512309 := by
  apply nodeValid_prime [2, 6827, 13751] ⟨375512309, 2, [(2, 2), (6827, 1), (13751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6827
    · exact prime_13751
  · decide +kernel

theorem prime_394611781 : Nat.Prime 394611781 := by
  apply nodeValid_prime [2, 3, 5, 6576863] ⟨394611781, 6, [(2, 2), (3, 1), (5, 1), (6576863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6576863
  · decide +kernel

theorem prime_518646377 : Nat.Prime 518646377 := by
  apply nodeValid_prime [2, 79, 820643] ⟨518646377, 3, [(2, 3), (79, 1), (820643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_820643
  · decide +kernel

theorem prime_718608907 : Nat.Prime 718608907 := by
  apply nodeValid_prime [2, 3, 227, 397, 443] ⟨718608907, 2, [(2, 1), (3, 2), (227, 1), (397, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_397
    · exact prime_443
  · decide +kernel

theorem prime_760408303 : Nat.Prime 760408303 := by
  apply nodeValid_prime [2, 3, 43, 1259, 2341] ⟨760408303, 5, [(2, 1), (3, 1), (43, 1), (1259, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1259
    · exact prime_2341
  · decide +kernel

theorem prime_775121591 : Nat.Prime 775121591 := by
  apply nodeValid_prime [2, 5, 77512159] ⟨775121591, 17, [(2, 1), (5, 1), (77512159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_77512159
  · decide +kernel

theorem prime_1039933597 : Nat.Prime 1039933597 := by
  apply nodeValid_prime [2, 3, 13, 6666241] ⟨1039933597, 2, [(2, 2), (3, 1), (13, 1), (6666241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6666241
  · decide +kernel

theorem prime_1107635957 : Nat.Prime 1107635957 := by
  apply nodeValid_prime [2, 7, 139, 284593] ⟨1107635957, 2, [(2, 2), (7, 1), (139, 1), (284593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_139
    · exact prime_284593
  · decide +kernel

theorem prime_1131793049 : Nat.Prime 1131793049 := by
  apply nodeValid_prime [2, 257, 733, 751] ⟨1131793049, 3, [(2, 3), (257, 1), (733, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_733
    · exact prime_751
  · decide +kernel

theorem prime_1658905691 : Nat.Prime 1658905691 := by
  apply nodeValid_prime [2, 5, 13, 981601] ⟨1658905691, 6, [(2, 1), (5, 1), (13, 2), (981601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_981601
  · decide +kernel

theorem prime_3004098473 : Nat.Prime 3004098473 := by
  apply nodeValid_prime [2, 375512309] ⟨3004098473, 3, [(2, 3), (375512309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_375512309
  · decide +kernel

theorem prime_3078464087 : Nat.Prime 3078464087 := by
  apply nodeValid_prime [2, 29, 349, 152083] ⟨3078464087, 5, [(2, 1), (29, 1), (349, 1), (152083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_349
    · exact prime_152083
  · decide +kernel

theorem prime_3842880619 : Nat.Prime 3842880619 := by
  apply nodeValid_prime [2, 3, 23, 27846961] ⟨3842880619, 10, [(2, 1), (3, 1), (23, 1), (27846961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_27846961
  · decide +kernel

theorem prime_6008196947 : Nat.Prime 6008196947 := by
  apply nodeValid_prime [2, 3004098473] ⟨6008196947, 2, [(2, 1), (3004098473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3004098473
  · decide +kernel

theorem prime_11601004409 : Nat.Prime 11601004409 := by
  apply nodeValid_prime [2, 7, 17, 23, 75689] ⟨11601004409, 3, [(2, 3), (7, 2), (17, 1), (23, 1), (75689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_75689
  · decide +kernel

theorem prime_13271245529 : Nat.Prime 13271245529 := by
  apply nodeValid_prime [2, 1658905691] ⟨13271245529, 3, [(2, 3), (1658905691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1658905691
  · decide +kernel

theorem prime_15329984179 : Nat.Prime 15329984179 := by
  apply nodeValid_prime [2, 3, 67, 97, 393137] ⟨15329984179, 14, [(2, 1), (3, 1), (67, 1), (97, 1), (393137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_97
    · exact prime_393137
  · decide +kernel

theorem prime_18121936247 : Nat.Prime 18121936247 := by
  apply nodeValid_prime [2, 73, 124122851] ⟨18121936247, 5, [(2, 1), (73, 1), (124122851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_124122851
  · decide +kernel

theorem prime_64547212679 : Nat.Prime 64547212679 := by
  apply nodeValid_prime [2, 13, 67, 241, 153749] ⟨64547212679, 11, [(2, 1), (13, 1), (67, 1), (241, 1), (153749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_241
    · exact prime_153749
  · decide +kernel

theorem prime_76119253801 : Nat.Prime 76119253801 := by
  apply nodeValid_prime [2, 3, 5, 31, 4092433] ⟨76119253801, 23, [(2, 3), (3, 1), (5, 2), (31, 1), (4092433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_4092433
  · decide +kernel

theorem prime_147789030527 : Nat.Prime 147789030527 := by
  apply nodeValid_prime [2, 47, 10009, 157081] ⟨147789030527, 5, [(2, 1), (47, 1), (10009, 1), (157081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_10009
    · exact prime_157081
  · decide +kernel

theorem prime_148390520651 : Nat.Prime 148390520651 := by
  apply nodeValid_prime [2, 5, 5179, 573047] ⟨148390520651, 2, [(2, 1), (5, 2), (5179, 1), (573047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5179
    · exact prime_573047
  · decide +kernel

theorem prime_152647441517 : Nat.Prime 152647441517 := by
  apply nodeValid_prime [2, 120623, 316373] ⟨152647441517, 2, [(2, 2), (120623, 1), (316373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_120623
    · exact prime_316373
  · decide +kernel

theorem prime_443968040261 : Nat.Prime 443968040261 := by
  apply nodeValid_prime [2, 5, 33629, 660097] ⟨443968040261, 2, [(2, 2), (5, 1), (33629, 1), (660097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33629
    · exact prime_660097
  · decide +kernel

theorem prime_449401314623 : Nat.Prime 449401314623 := by
  apply nodeValid_prime [2, 13, 1063, 16260269] ⟨449401314623, 5, [(2, 1), (13, 1), (1063, 1), (16260269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1063
    · exact prime_16260269
  · decide +kernel

theorem prime_886734183163 : Nat.Prime 886734183163 := by
  apply nodeValid_prime [2, 3, 147789030527] ⟨886734183163, 2, [(2, 1), (3, 1), (147789030527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_147789030527
  · decide +kernel

theorem prime_886734183383 : Nat.Prime 886734183383 := by
  apply nodeValid_prime [2, 19, 67679, 344791] ⟨886734183383, 5, [(2, 1), (19, 1), (67679, 1), (344791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_67679
    · exact prime_344791
  · decide +kernel

theorem prime_886734191333 : Nat.Prime 886734191333 := by
  apply nodeValid_prime [2, 11, 1319, 3637, 4201] ⟨886734191333, 2, [(2, 2), (11, 1), (1319, 1), (3637, 1), (4201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1319
    · exact prime_3637
    · exact prime_4201
  · decide +kernel

theorem prime_887936065547 : Nat.Prime 887936065547 := by
  apply nodeValid_prime [2, 19, 124771, 187277] ⟨887936065547, 2, [(2, 1), (19, 1), (124771, 1), (187277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_124771
    · exact prime_187277
  · decide +kernel

theorem prime_887936078893 : Nat.Prime 887936078893 := by
  apply nodeValid_prime [2, 3, 389, 190217669] ⟨887936078893, 2, [(2, 2), (3, 1), (389, 1), (190217669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_190217669
  · decide +kernel

theorem prime_887936080523 : Nat.Prime 887936080523 := by
  apply nodeValid_prime [2, 443968040261] ⟨887936080523, 2, [(2, 1), (443968040261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_443968040261
  · decide +kernel

theorem prime_889139042899 : Nat.Prime 889139042899 := by
  apply nodeValid_prime [2, 3, 8693, 17047031] ⟨889139042899, 2, [(2, 1), (3, 1), (8693, 1), (17047031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8693
    · exact prime_17047031
  · decide +kernel

theorem prime_889139082383 : Nat.Prime 889139082383 := by
  apply nodeValid_prime [2, 29, 15329984179] ⟨889139082383, 5, [(2, 1), (29, 1), (15329984179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_15329984179
  · decide +kernel

theorem prime_889139087699 : Nat.Prime 889139087699 := by
  apply nodeValid_prime [2, 37, 61, 5413, 36389] ⟨889139087699, 2, [(2, 1), (37, 1), (61, 1), (5413, 1), (36389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_61
    · exact prime_5413
    · exact prime_36389
  · decide +kernel

theorem prime_890343123643 : Nat.Prime 890343123643 := by
  apply nodeValid_prime [2, 3, 7, 37, 109, 584033] ⟨890343123643, 2, [(2, 1), (3, 3), (7, 1), (37, 1), (109, 1), (584033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_109
    · exact prime_584033
  · decide +kernel

theorem prime_890343123907 : Nat.Prime 890343123907 := by
  apply nodeValid_prime [2, 3, 148390520651] ⟨890343123907, 3, [(2, 1), (3, 1), (148390520651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_148390520651
  · decide +kernel

theorem prime_890343123979 : Nat.Prime 890343123979 := by
  apply nodeValid_prime [2, 3, 7, 11, 43, 3631, 12343] ⟨890343123979, 7, [(2, 1), (3, 1), (7, 1), (11, 1), (43, 1), (3631, 1), (12343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_43
    · exact prime_3631
    · exact prime_12343
  · decide +kernel

theorem prime_891548303609 : Nat.Prime 891548303609 := by
  apply nodeValid_prime [2, 29, 3842880619] ⟨891548303609, 3, [(2, 3), (29, 1), (3842880619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3842880619
  · decide +kernel

theorem prime_891548420297 : Nat.Prime 891548420297 := by
  apply nodeValid_prime [2, 16553, 6732529] ⟨891548420297, 3, [(2, 3), (16553, 1), (6732529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16553
    · exact prime_6732529
  · decide +kernel

theorem prime_891548421143 : Nat.Prime 891548421143 := by
  apply nodeValid_prime [2, 103, 281, 15401797] ⟨891548421143, 5, [(2, 1), (103, 1), (281, 1), (15401797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_281
    · exact prime_15401797
  · decide +kernel

theorem prime_892754580973 : Nat.Prime 892754580973 := by
  apply nodeValid_prime [2, 3, 23, 89, 193, 188311] ⟨892754580973, 2, [(2, 2), (3, 1), (23, 1), (89, 1), (193, 1), (188311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_89
    · exact prime_193
    · exact prime_188311
  · decide +kernel

theorem prime_892754581343 : Nat.Prime 892754581343 := by
  apply nodeValid_prime [2, 13, 31, 1107635957] ⟨892754581343, 7, [(2, 1), (13, 1), (31, 1), (1107635957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_1107635957
  · decide +kernel

theorem prime_892754585231 : Nat.Prime 892754585231 := by
  apply nodeValid_prime [2, 5, 29, 3078464087] ⟨892754585231, 13, [(2, 1), (5, 1), (29, 1), (3078464087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3078464087
  · decide +kernel

theorem prime_893961979459 : Nat.Prime 893961979459 := by
  apply nodeValid_prime [2, 3, 647, 230283869] ⟨893961979459, 2, [(2, 1), (3, 1), (647, 1), (230283869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_647
    · exact prime_230283869
  · decide +kernel

theorem prime_893962026967 : Nat.Prime 893962026967 := by
  apply nodeValid_prime [2, 3, 2377, 62681393] ⟨893962026967, 3, [(2, 1), (3, 1), (2377, 1), (62681393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2377
    · exact prime_62681393
  · decide +kernel

theorem prime_893962027111 : Nat.Prime 893962027111 := by
  apply nodeValid_prime [2, 3, 5, 139, 214379383] ⟨893962027111, 3, [(2, 1), (3, 1), (5, 1), (139, 1), (214379383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_214379383
  · decide +kernel

theorem prime_895170474719 : Nat.Prime 895170474719 := by
  apply nodeValid_prime [2, 13, 37, 67, 2239, 6203] ⟨895170474719, 11, [(2, 1), (13, 1), (37, 1), (67, 1), (2239, 1), (6203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_67
    · exact prime_2239
    · exact prime_6203
  · decide +kernel

theorem prime_895170476047 : Nat.Prime 895170476047 := by
  apply nodeValid_prime [2, 3, 7, 11, 53, 36558461] ⟨895170476047, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (53, 1), (36558461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_53
    · exact prime_36558461
  · decide +kernel

theorem prime_895170483799 : Nat.Prime 895170483799 := by
  apply nodeValid_prime [2, 3, 80611, 1850803] ⟨895170483799, 3, [(2, 1), (3, 1), (80611, 1), (1850803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80611
    · exact prime_1850803
  · decide +kernel

theorem prime_896380094809 : Nat.Prime 896380094809 := by
  apply nodeValid_prime [2, 3, 11, 1131793049] ⟨896380094809, 7, [(2, 3), (3, 2), (11, 1), (1131793049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1131793049
  · decide +kernel

theorem prime_896380125281 : Nat.Prime 896380125281 := by
  apply nodeValid_prime [2, 5, 67, 83617549] ⟨896380125281, 3, [(2, 5), (5, 1), (67, 1), (83617549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_83617549
  · decide +kernel

theorem prime_896380125469 : Nat.Prime 896380125469 := by
  apply nodeValid_prime [2, 3, 53, 229, 6154597] ⟨896380125469, 2, [(2, 2), (3, 1), (53, 1), (229, 1), (6154597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_229
    · exact prime_6154597
  · decide +kernel

theorem prime_897590802379 : Nat.Prime 897590802379 := by
  apply nodeValid_prime [2, 3, 193, 775121591] ⟨897590802379, 2, [(2, 1), (3, 1), (193, 1), (775121591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_775121591
  · decide +kernel

theorem prime_897590851219 : Nat.Prime 897590851219 := by
  apply nodeValid_prime [2, 3, 383, 461, 282427] ⟨897590851219, 3, [(2, 1), (3, 2), (383, 1), (461, 1), (282427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_383
    · exact prime_461
    · exact prime_282427
  · decide +kernel

theorem prime_897590851639 : Nat.Prime 897590851639 := by
  apply nodeValid_prime [2, 3, 13, 53, 983, 220879] ⟨897590851639, 11, [(2, 1), (3, 1), (13, 1), (53, 1), (983, 1), (220879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_983
    · exact prime_220879
  · decide +kernel

theorem prime_898802614147 : Nat.Prime 898802614147 := by
  apply nodeValid_prime [2, 3, 197, 760408303] ⟨898802614147, 2, [(2, 1), (3, 1), (197, 1), (760408303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_760408303
  · decide +kernel

theorem prime_898802625647 : Nat.Prime 898802625647 := by
  apply nodeValid_prime [2, 13291, 33812453] ⟨898802625647, 5, [(2, 1), (13291, 1), (33812453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13291
    · exact prime_33812453
  · decide +kernel

theorem prime_898802629247 : Nat.Prime 898802629247 := by
  apply nodeValid_prime [2, 449401314623] ⟨898802629247, 5, [(2, 1), (449401314623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_449401314623
  · decide +kernel

theorem prime_900015535829 : Nat.Prime 900015535829 := by
  apply nodeValid_prime [2, 1049, 214493693] ⟨900015535829, 2, [(2, 2), (1049, 1), (214493693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1049
    · exact prime_214493693
  · decide +kernel

theorem prime_900015536197 : Nat.Prime 900015536197 := by
  apply nodeValid_prime [2, 3, 7, 79, 167, 4297] ⟨900015536197, 2, [(2, 2), (3, 4), (7, 2), (79, 1), (167, 1), (4297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_167
    · exact prime_4297
  · decide +kernel

theorem prime_900015536291 : Nat.Prime 900015536291 := by
  apply nodeValid_prime [2, 5, 13, 17, 151, 158647] ⟨900015536291, 2, [(2, 1), (5, 1), (13, 1), (17, 2), (151, 1), (158647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_151
    · exact prime_158647
  · decide +kernel

theorem prime_901229542051 : Nat.Prime 901229542051 := by
  apply nodeValid_prime [2, 3, 5, 6008196947] ⟨901229542051, 2, [(2, 1), (3, 1), (5, 2), (6008196947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6008196947
  · decide +kernel

theorem prime_901229542783 : Nat.Prime 901229542783 := by
  apply nodeValid_prime [2, 3, 71, 89, 1033, 23011] ⟨901229542783, 3, [(2, 1), (3, 1), (71, 1), (89, 1), (1033, 1), (23011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_89
    · exact prime_1033
    · exact prime_23011
  · decide +kernel

theorem prime_901229566969 : Nat.Prime 901229566969 := by
  apply nodeValid_prime [2, 3, 23, 37, 1873, 7853] ⟨901229566969, 11, [(2, 3), (3, 2), (23, 1), (37, 1), (1873, 1), (7853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
    · exact prime_1873
    · exact prime_7853
  · decide +kernel

theorem prime_902444695973 : Nat.Prime 902444695973 := by
  apply nodeValid_prime [2, 17, 13271245529] ⟨902444695973, 2, [(2, 2), (17, 1), (13271245529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_13271245529
  · decide +kernel

theorem prime_902444695981 : Nat.Prime 902444695981 := by
  apply nodeValid_prime [2, 3, 5, 29, 518646377] ⟨902444695981, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (518646377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_518646377
  · decide +kernel

theorem prime_902444719997 : Nat.Prime 902444719997 := by
  apply nodeValid_prime [2, 1153, 195673183] ⟨902444719997, 2, [(2, 2), (1153, 1), (195673183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1153
    · exact prime_195673183
  · decide +kernel

theorem prime_903660977507 : Nat.Prime 903660977507 := by
  apply nodeValid_prime [2, 7, 64547212679] ⟨903660977507, 5, [(2, 1), (7, 1), (64547212679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_64547212679
  · decide +kernel

theorem prime_903660978491 : Nat.Prime 903660978491 := by
  apply nodeValid_prime [2, 5, 229, 394611781] ⟨903660978491, 2, [(2, 1), (5, 1), (229, 1), (394611781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_394611781
  · decide +kernel

theorem prime_903660980039 : Nat.Prime 903660980039 := by
  apply nodeValid_prime [2, 67, 5011, 1345787] ⟨903660980039, 11, [(2, 1), (67, 1), (5011, 1), (1345787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_5011
    · exact prime_1345787
  · decide +kernel

theorem prime_904878301741 : Nat.Prime 904878301741 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 74292143] ⟨904878301741, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (74292143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_74292143
  · decide +kernel

theorem prime_904878302693 : Nat.Prime 904878302693 := by
  apply nodeValid_prime [2, 7, 13, 409, 617, 9851] ⟨904878302693, 2, [(2, 2), (7, 1), (13, 1), (409, 1), (617, 1), (9851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_409
    · exact prime_617
    · exact prime_9851
  · decide +kernel

theorem prime_904878343903 : Nat.Prime 904878343903 := by
  apply nodeValid_prime [2, 3, 13, 11601004409] ⟨904878343903, 3, [(2, 1), (3, 1), (13, 1), (11601004409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_11601004409
  · decide +kernel

theorem prime_906096812321 : Nat.Prime 906096812321 := by
  apply nodeValid_prime [2, 5, 7, 569, 203117] ⟨906096812321, 6, [(2, 5), (5, 1), (7, 2), (569, 1), (203117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_569
    · exact prime_203117
  · decide +kernel

theorem prime_906096812351 : Nat.Prime 906096812351 := by
  apply nodeValid_prime [2, 5, 18121936247] ⟨906096812351, 11, [(2, 1), (5, 2), (18121936247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18121936247
  · decide +kernel

theorem prime_906096820217 : Nat.Prime 906096820217 := by
  apply nodeValid_prime [2, 7, 59, 619, 443041] ⟨906096820217, 3, [(2, 3), (7, 1), (59, 1), (619, 1), (443041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_619
    · exact prime_443041
  · decide +kernel

theorem prime_907316409929 : Nat.Prime 907316409929 := by
  apply nodeValid_prime [2, 31, 2099, 1742989] ⟨907316409929, 3, [(2, 3), (31, 1), (2099, 1), (1742989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2099
    · exact prime_1742989
  · decide +kernel

theorem prime_907316446901 : Nat.Prime 907316446901 := by
  apply nodeValid_prime [2, 5, 17, 109, 1129, 4337] ⟨907316446901, 2, [(2, 2), (5, 2), (17, 1), (109, 1), (1129, 1), (4337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_109
    · exact prime_1129
    · exact prime_4337
  · decide +kernel

theorem prime_907316447911 : Nat.Prime 907316447911 := by
  apply nodeValid_prime [2, 3, 5, 881, 34329037] ⟨907316447911, 3, [(2, 1), (3, 1), (5, 1), (881, 1), (34329037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_881
    · exact prime_34329037
  · decide +kernel

theorem prime_908537110849 : Nat.Prime 908537110849 := by
  apply nodeValid_prime [2, 3, 41, 12823751] ⟨908537110849, 29, [(2, 6), (3, 3), (41, 1), (12823751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_12823751
  · decide +kernel

theorem prime_908537193643 : Nat.Prime 908537193643 := by
  apply nodeValid_prime [2, 3, 13, 71, 149, 157, 7013] ⟨908537193643, 2, [(2, 1), (3, 1), (13, 1), (71, 1), (149, 1), (157, 1), (7013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_149
    · exact prime_157
    · exact prime_7013
  · decide +kernel

theorem prime_908537194231 : Nat.Prime 908537194231 := by
  apply nodeValid_prime [2, 3, 5, 1181, 25643161] ⟨908537194231, 3, [(2, 1), (3, 1), (5, 1), (1181, 1), (25643161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1181
    · exact prime_25643161
  · decide +kernel

theorem prime_909758875633 : Nat.Prime 909758875633 := by
  apply nodeValid_prime [2, 3, 44087, 429907] ⟨909758875633, 5, [(2, 4), (3, 1), (44087, 1), (429907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44087
    · exact prime_429907
  · decide +kernel

theorem prime_909758876263 : Nat.Prime 909758876263 := by
  apply nodeValid_prime [2, 3, 211, 718608907] ⟨909758876263, 5, [(2, 1), (3, 1), (211, 1), (718608907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_718608907
  · decide +kernel

theorem prime_909758919229 : Nat.Prime 909758919229 := by
  apply nodeValid_prime [2, 3, 4133, 18343393] ⟨909758919229, 2, [(2, 2), (3, 1), (4133, 1), (18343393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4133
    · exact prime_18343393
  · decide +kernel

theorem prime_910981830973 : Nat.Prime 910981830973 := by
  apply nodeValid_prime [2, 3, 73, 1039933597] ⟨910981830973, 2, [(2, 2), (3, 1), (73, 1), (1039933597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_1039933597
  · decide +kernel

theorem prime_910981831189 : Nat.Prime 910981831189 := by
  apply nodeValid_prime [2, 3, 11, 13, 3371, 157483] ⟨910981831189, 6, [(2, 2), (3, 1), (11, 1), (13, 1), (3371, 1), (157483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_3371
    · exact prime_157483
  · decide +kernel

theorem prime_910981841821 : Nat.Prime 910981841821 := by
  apply nodeValid_prime [2, 3, 5, 37, 3181, 129001] ⟨910981841821, 6, [(2, 2), (3, 1), (5, 1), (37, 1), (3181, 1), (129001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_3181
    · exact prime_129001
  · decide +kernel

theorem prime_912205789927 : Nat.Prime 912205789927 := by
  apply nodeValid_prime [2, 3, 443, 541, 634367] ⟨912205789927, 3, [(2, 1), (3, 1), (443, 1), (541, 1), (634367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_443
    · exact prime_541
    · exact prime_634367
  · decide +kernel

theorem prime_912205790663 : Nat.Prime 912205790663 := by
  apply nodeValid_prime [2, 157, 3083, 942301] ⟨912205790663, 5, [(2, 1), (157, 1), (3083, 1), (942301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_3083
    · exact prime_942301
  · decide +kernel

theorem prime_912205876061 : Nat.Prime 912205876061 := by
  apply nodeValid_prime [2, 5, 17, 14249, 188291] ⟨912205876061, 2, [(2, 2), (5, 1), (17, 1), (14249, 1), (188291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_14249
    · exact prime_188291
  · decide +kernel

theorem prime_913431027727 : Nat.Prime 913431027727 := by
  apply nodeValid_prime [2, 3, 7, 25147, 288283] ⟨913431027727, 5, [(2, 1), (3, 2), (7, 1), (25147, 1), (288283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_25147
    · exact prime_288283
  · decide +kernel

theorem prime_913431045613 : Nat.Prime 913431045613 := by
  apply nodeValid_prime [2, 3, 76119253801] ⟨913431045613, 5, [(2, 2), (3, 1), (76119253801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76119253801
  · decide +kernel

theorem prime_913431047569 : Nat.Prime 913431047569 := by
  apply nodeValid_prime [2, 3, 13, 5981, 244747] ⟨913431047569, 7, [(2, 4), (3, 1), (13, 1), (5981, 1), (244747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5981
    · exact prime_244747
  · decide +kernel

theorem prime_914657293631 : Nat.Prime 914657293631 := by
  apply nodeValid_prime [2, 5, 80923, 1130281] ⟨914657293631, 7, [(2, 1), (5, 1), (80923, 1), (1130281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_80923
    · exact prime_1130281
  · decide +kernel

theorem prime_914657327879 : Nat.Prime 914657327879 := by
  apply nodeValid_prime [2, 7, 19, 277, 12413579] ⟨914657327879, 7, [(2, 1), (7, 1), (19, 1), (277, 1), (12413579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_277
    · exact prime_12413579
  · decide +kernel

theorem prime_914657331743 : Nat.Prime 914657331743 := by
  apply nodeValid_prime [2, 7, 11, 761, 101359] ⟨914657331743, 5, [(2, 1), (7, 2), (11, 2), (761, 1), (101359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_761
    · exact prime_101359
  · decide +kernel

theorem prime_915884649103 : Nat.Prime 915884649103 := by
  apply nodeValid_prime [2, 3, 152647441517] ⟨915884649103, 6, [(2, 1), (3, 1), (152647441517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152647441517
  · decide +kernel

theorem prime_915884649791 : Nat.Prime 915884649791 := by
  apply nodeValid_prime [2, 5, 11, 23, 362009743] ⟨915884649791, 11, [(2, 1), (5, 1), (11, 1), (23, 1), (362009743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_362009743
  · decide +kernel

theorem prime_915884672383 : Nat.Prime 915884672383 := by
  apply nodeValid_prime [2, 3, 10663, 4771873] ⟨915884672383, 3, [(2, 1), (3, 2), (10663, 1), (4771873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10663
    · exact prime_4771873
  · decide +kernel

end Sude.Lucas.Generated
