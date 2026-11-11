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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1481 : Nat.Prime 1481 := by
  apply nodeValid_prime [2, 5, 37] ⟨1481, 3, [(2, 3), (5, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_1831 : Nat.Prime 1831 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨1831, 3, [(2, 1), (3, 1), (5, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_2039 : Nat.Prime 2039 := by
  apply nodeValid_prime [2, 1019] ⟨2039, 7, [(2, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1019
  · decide +kernel

theorem prime_3323 : Nat.Prime 3323 := by
  apply nodeValid_prime [2, 11, 151] ⟨3323, 2, [(2, 1), (11, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_151
  · decide +kernel

theorem prime_3461 : Nat.Prime 3461 := by
  apply nodeValid_prime [2, 5, 173] ⟨3461, 2, [(2, 2), (5, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_4271 : Nat.Prime 4271 := by
  apply nodeValid_prime [2, 5, 7, 61] ⟨4271, 7, [(2, 1), (5, 1), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_5011 : Nat.Prime 5011 := by
  apply nodeValid_prime [2, 3, 5, 167] ⟨5011, 2, [(2, 1), (3, 1), (5, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
  · decide +kernel

theorem prime_5683 : Nat.Prime 5683 := by
  apply nodeValid_prime [2, 3, 947] ⟨5683, 2, [(2, 1), (3, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_947
  · decide +kernel

theorem prime_7013 : Nat.Prime 7013 := by
  apply nodeValid_prime [2, 1753] ⟨7013, 2, [(2, 2), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1753
  · decide +kernel

theorem prime_7243 : Nat.Prime 7243 := by
  apply nodeValid_prime [2, 3, 17, 71] ⟨7243, 2, [(2, 1), (3, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_8543 : Nat.Prime 8543 := by
  apply nodeValid_prime [2, 4271] ⟨8543, 5, [(2, 1), (4271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4271
  · decide +kernel

theorem prime_8681 : Nat.Prime 8681 := by
  apply nodeValid_prime [2, 5, 7, 31] ⟨8681, 15, [(2, 3), (5, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_10259 : Nat.Prime 10259 := by
  apply nodeValid_prime [2, 23, 223] ⟨10259, 2, [(2, 1), (23, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_223
  · decide +kernel

theorem prime_10979 : Nat.Prime 10979 := by
  apply nodeValid_prime [2, 11, 499] ⟨10979, 2, [(2, 1), (11, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_499
  · decide +kernel

theorem prime_10987 : Nat.Prime 10987 := by
  apply nodeValid_prime [2, 3, 1831] ⟨10987, 2, [(2, 1), (3, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1831
  · decide +kernel

theorem prime_13177 : Nat.Prime 13177 := by
  apply nodeValid_prime [2, 3, 61] ⟨13177, 5, [(2, 3), (3, 3), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel

theorem prime_13967 : Nat.Prime 13967 := by
  apply nodeValid_prime [2, 6983] ⟨13967, 5, [(2, 1), (6983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6983
  · decide +kernel

theorem prime_17033 : Nat.Prime 17033 := by
  apply nodeValid_prime [2, 2129] ⟨17033, 3, [(2, 3), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2129
  · decide +kernel

theorem prime_17257 : Nat.Prime 17257 := by
  apply nodeValid_prime [2, 3, 719] ⟨17257, 5, [(2, 3), (3, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
  · decide +kernel

theorem prime_17383 : Nat.Prime 17383 := by
  apply nodeValid_prime [2, 3, 2897] ⟨17383, 5, [(2, 1), (3, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2897
  · decide +kernel

theorem prime_18719 : Nat.Prime 18719 := by
  apply nodeValid_prime [2, 7, 191] ⟨18719, 7, [(2, 1), (7, 2), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_191
  · decide +kernel

theorem prime_20411 : Nat.Prime 20411 := by
  apply nodeValid_prime [2, 5, 13, 157] ⟨20411, 6, [(2, 1), (5, 1), (13, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_157
  · decide +kernel

theorem prime_25679 : Nat.Prime 25679 := by
  apply nodeValid_prime [2, 37, 347] ⟨25679, 11, [(2, 1), (37, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_347
  · decide +kernel

theorem prime_25999 : Nat.Prime 25999 := by
  apply nodeValid_prime [2, 3, 7, 619] ⟨25999, 7, [(2, 1), (3, 1), (7, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_619
  · decide +kernel

theorem prime_26723 : Nat.Prime 26723 := by
  apply nodeValid_prime [2, 31, 431] ⟨26723, 2, [(2, 1), (31, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_431
  · decide +kernel

theorem prime_27277 : Nat.Prime 27277 := by
  apply nodeValid_prime [2, 3, 2273] ⟨27277, 6, [(2, 2), (3, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2273
  · decide +kernel

theorem prime_28723 : Nat.Prime 28723 := by
  apply nodeValid_prime [2, 3, 4787] ⟨28723, 2, [(2, 1), (3, 1), (4787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4787
  · decide +kernel

theorem prime_31159 : Nat.Prime 31159 := by
  apply nodeValid_prime [2, 3, 577] ⟨31159, 3, [(2, 1), (3, 3), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
  · decide +kernel

theorem prime_33721 : Nat.Prime 33721 := by
  apply nodeValid_prime [2, 3, 5, 281] ⟨33721, 11, [(2, 3), (3, 1), (5, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_281
  · decide +kernel

theorem prime_35353 : Nat.Prime 35353 := by
  apply nodeValid_prime [2, 3, 491] ⟨35353, 5, [(2, 3), (3, 2), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_491
  · decide +kernel

theorem prime_53693 : Nat.Prime 53693 := by
  apply nodeValid_prime [2, 31, 433] ⟨53693, 2, [(2, 2), (31, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_433
  · decide +kernel

theorem prime_59159 : Nat.Prime 59159 := by
  apply nodeValid_prime [2, 11, 2689] ⟨59159, 7, [(2, 1), (11, 1), (2689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2689
  · decide +kernel

theorem prime_59183 : Nat.Prime 59183 := by
  apply nodeValid_prime [2, 127, 233] ⟨59183, 5, [(2, 1), (127, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_233
  · decide +kernel

theorem prime_62507 : Nat.Prime 62507 := by
  apply nodeValid_prime [2, 31253] ⟨62507, 2, [(2, 1), (31253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31253
  · decide +kernel

theorem prime_63473 : Nat.Prime 63473 := by
  apply nodeValid_prime [2, 3967] ⟨63473, 3, [(2, 4), (3967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3967
  · decide +kernel

theorem prime_66403 : Nat.Prime 66403 := by
  apply nodeValid_prime [2, 3, 7, 17, 31] ⟨66403, 2, [(2, 1), (3, 2), (7, 1), (17, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_31
  · decide +kernel

theorem prime_68351 : Nat.Prime 68351 := by
  apply nodeValid_prime [2, 5, 1367] ⟨68351, 17, [(2, 1), (5, 2), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1367
  · decide +kernel

theorem prime_81041 : Nat.Prime 81041 := by
  apply nodeValid_prime [2, 5, 1013] ⟨81041, 6, [(2, 4), (5, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1013
  · decide +kernel

theorem prime_81919 : Nat.Prime 81919 := by
  apply nodeValid_prime [2, 3, 37, 41] ⟨81919, 3, [(2, 1), (3, 3), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_88883 : Nat.Prime 88883 := by
  apply nodeValid_prime [2, 19, 2339] ⟨88883, 2, [(2, 1), (19, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2339
  · decide +kernel

theorem prime_90977 : Nat.Prime 90977 := by
  apply nodeValid_prime [2, 2843] ⟨90977, 3, [(2, 5), (2843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2843
  · decide +kernel

theorem prime_94447 : Nat.Prime 94447 := by
  apply nodeValid_prime [2, 3, 11, 53] ⟨94447, 5, [(2, 1), (3, 4), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_97687 : Nat.Prime 97687 := by
  apply nodeValid_prime [2, 3, 67] ⟨97687, 5, [(2, 1), (3, 6), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
  · decide +kernel

theorem prime_103291 : Nat.Prime 103291 := by
  apply nodeValid_prime [2, 3, 5, 11, 313] ⟨103291, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_313
  · decide +kernel

theorem prime_112583 : Nat.Prime 112583 := by
  apply nodeValid_prime [2, 181, 311] ⟨112583, 5, [(2, 1), (181, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_311
  · decide +kernel

theorem prime_128969 : Nat.Prime 128969 := by
  apply nodeValid_prime [2, 7, 47] ⟨128969, 3, [(2, 3), (7, 3), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_133051 : Nat.Prime 133051 := by
  apply nodeValid_prime [2, 3, 5, 887] ⟨133051, 2, [(2, 1), (3, 1), (5, 2), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_887
  · decide +kernel

theorem prime_150077 : Nat.Prime 150077 := by
  apply nodeValid_prime [2, 17, 2207] ⟨150077, 2, [(2, 2), (17, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2207
  · decide +kernel

theorem prime_168253 : Nat.Prime 168253 := by
  apply nodeValid_prime [2, 3, 7, 2003] ⟨168253, 14, [(2, 2), (3, 1), (7, 1), (2003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2003
  · decide +kernel

theorem prime_173209 : Nat.Prime 173209 := by
  apply nodeValid_prime [2, 3, 7, 1031] ⟨173209, 23, [(2, 3), (3, 1), (7, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1031
  · decide +kernel

theorem prime_184417 : Nat.Prime 184417 := by
  apply nodeValid_prime [2, 3, 17, 113] ⟨184417, 10, [(2, 5), (3, 1), (17, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_113
  · decide +kernel

theorem prime_190823 : Nat.Prime 190823 := by
  apply nodeValid_prime [2, 73, 1307] ⟨190823, 5, [(2, 1), (73, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1307
  · decide +kernel

theorem prime_198377 : Nat.Prime 198377 := by
  apply nodeValid_prime [2, 137, 181] ⟨198377, 3, [(2, 3), (137, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_181
  · decide +kernel

theorem prime_211187 : Nat.Prime 211187 := by
  apply nodeValid_prime [2, 23, 4591] ⟨211187, 2, [(2, 1), (23, 1), (4591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4591
  · decide +kernel

theorem prime_243311 : Nat.Prime 243311 := by
  apply nodeValid_prime [2, 5, 29, 839] ⟨243311, 17, [(2, 1), (5, 1), (29, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_839
  · decide +kernel

theorem prime_250279 : Nat.Prime 250279 := by
  apply nodeValid_prime [2, 3, 7, 59, 101] ⟨250279, 3, [(2, 1), (3, 1), (7, 1), (59, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_101
  · decide +kernel

theorem prime_288913 : Nat.Prime 288913 := by
  apply nodeValid_prime [2, 3, 13, 463] ⟨288913, 10, [(2, 4), (3, 1), (13, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_463
  · decide +kernel

theorem prime_289721 : Nat.Prime 289721 := by
  apply nodeValid_prime [2, 5, 7243] ⟨289721, 3, [(2, 3), (5, 1), (7243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7243
  · decide +kernel

theorem prime_340661 : Nat.Prime 340661 := by
  apply nodeValid_prime [2, 5, 17033] ⟨340661, 2, [(2, 2), (5, 1), (17033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17033
  · decide +kernel

theorem prime_371383 : Nat.Prime 371383 := by
  apply nodeValid_prime [2, 3, 11, 17, 331] ⟨371383, 3, [(2, 1), (3, 1), (11, 1), (17, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_331
  · decide +kernel

theorem prime_375043 : Nat.Prime 375043 := by
  apply nodeValid_prime [2, 3, 62507] ⟨375043, 3, [(2, 1), (3, 1), (62507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62507
  · decide +kernel

theorem prime_378379 : Nat.Prime 378379 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨378379, 2, [(2, 1), (3, 3), (7, 2), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_384533 : Nat.Prime 384533 := by
  apply nodeValid_prime [2, 251, 383] ⟨384533, 2, [(2, 2), (251, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_383
  · decide +kernel

theorem prime_386621 : Nat.Prime 386621 := by
  apply nodeValid_prime [2, 5, 13, 1487] ⟨386621, 2, [(2, 2), (5, 1), (13, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1487
  · decide +kernel

theorem prime_393739 : Nat.Prime 393739 := by
  apply nodeValid_prime [2, 3, 137, 479] ⟨393739, 3, [(2, 1), (3, 1), (137, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_479
  · decide +kernel

theorem prime_407321 : Nat.Prime 407321 := by
  apply nodeValid_prime [2, 5, 17, 599] ⟨407321, 3, [(2, 3), (5, 1), (17, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_599
  · decide +kernel

theorem prime_414553 : Nat.Prime 414553 := by
  apply nodeValid_prime [2, 3, 23, 751] ⟨414553, 5, [(2, 3), (3, 1), (23, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_751
  · decide +kernel

theorem prime_483829 : Nat.Prime 483829 := by
  apply nodeValid_prime [2, 3, 23, 1753] ⟨483829, 2, [(2, 2), (3, 1), (23, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1753
  · decide +kernel

theorem prime_622177 : Nat.Prime 622177 := by
  apply nodeValid_prime [2, 3, 6481] ⟨622177, 11, [(2, 5), (3, 1), (6481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6481
  · decide +kernel

theorem prime_638839 : Nat.Prime 638839 := by
  apply nodeValid_prime [2, 3, 35491] ⟨638839, 3, [(2, 1), (3, 2), (35491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35491
  · decide +kernel

theorem prime_758273 : Nat.Prime 758273 := by
  apply nodeValid_prime [2, 1481] ⟨758273, 3, [(2, 9), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1481
  · decide +kernel

theorem prime_774071 : Nat.Prime 774071 := by
  apply nodeValid_prime [2, 5, 11, 31, 227] ⟨774071, 7, [(2, 1), (5, 1), (11, 1), (31, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_227
  · decide +kernel

theorem prime_784409 : Nat.Prime 784409 := by
  apply nodeValid_prime [2, 71, 1381] ⟨784409, 3, [(2, 3), (71, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1381
  · decide +kernel

theorem prime_912167 : Nat.Prime 912167 := by
  apply nodeValid_prime [2, 29, 15727] ⟨912167, 5, [(2, 1), (29, 1), (15727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_15727
  · decide +kernel

theorem prime_1167599 : Nat.Prime 1167599 := by
  apply nodeValid_prime [2, 29, 41, 491] ⟨1167599, 11, [(2, 1), (29, 1), (41, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_41
    · exact prime_491
  · decide +kernel

theorem prime_1299041 : Nat.Prime 1299041 := by
  apply nodeValid_prime [2, 5, 23, 353] ⟨1299041, 3, [(2, 5), (5, 1), (23, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_353
  · decide +kernel

theorem prime_1308247 : Nat.Prime 1308247 := by
  apply nodeValid_prime [2, 3, 37, 71, 83] ⟨1308247, 3, [(2, 1), (3, 1), (37, 1), (71, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_83
  · decide +kernel

theorem prime_1516547 : Nat.Prime 1516547 := by
  apply nodeValid_prime [2, 758273] ⟨1516547, 2, [(2, 1), (758273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_758273
  · decide +kernel

theorem prime_2003611 : Nat.Prime 2003611 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 47] ⟨2003611, 2, [(2, 1), (3, 1), (5, 1), (7, 2), (29, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_47
  · decide +kernel

theorem prime_2078509 : Nat.Prime 2078509 := by
  apply nodeValid_prime [2, 3, 173209] ⟨2078509, 2, [(2, 2), (3, 1), (173209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173209
  · decide +kernel

theorem prime_2774873 : Nat.Prime 2774873 := by
  apply nodeValid_prime [2, 31, 67, 167] ⟨2774873, 3, [(2, 3), (31, 1), (67, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_67
    · exact prime_167
  · decide +kernel

theorem prime_5688811 : Nat.Prime 5688811 := by
  apply nodeValid_prime [2, 3, 5, 31, 2039] ⟨5688811, 2, [(2, 1), (3, 2), (5, 1), (31, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_2039
  · decide +kernel

theorem prime_6192569 : Nat.Prime 6192569 := by
  apply nodeValid_prime [2, 774071] ⟨6192569, 3, [(2, 3), (774071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_774071
  · decide +kernel

theorem prime_6275273 : Nat.Prime 6275273 := by
  apply nodeValid_prime [2, 784409] ⟨6275273, 3, [(2, 3), (784409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_784409
  · decide +kernel

theorem prime_6632849 : Nat.Prime 6632849 := by
  apply nodeValid_prime [2, 414553] ⟨6632849, 3, [(2, 4), (414553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_414553
  · decide +kernel

theorem prime_6673169 : Nat.Prime 6673169 := by
  apply nodeValid_prime [2, 193, 2161] ⟨6673169, 3, [(2, 4), (193, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_2161
  · decide +kernel

theorem prime_6736859 : Nat.Prime 6736859 := by
  apply nodeValid_prime [2, 31, 193, 563] ⟨6736859, 2, [(2, 1), (31, 1), (193, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_193
    · exact prime_563
  · decide +kernel

theorem prime_7002581 : Nat.Prime 7002581 := by
  apply nodeValid_prime [2, 5, 13, 23, 1171] ⟨7002581, 2, [(2, 2), (5, 1), (13, 1), (23, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_1171
  · decide +kernel

theorem prime_7900873 : Nat.Prime 7900873 := by
  apply nodeValid_prime [2, 3, 7, 131, 359] ⟨7900873, 5, [(2, 3), (3, 1), (7, 1), (131, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_131
    · exact prime_359
  · decide +kernel

theorem prime_8662259 : Nat.Prime 8662259 := by
  apply nodeValid_prime [2, 11, 393739] ⟨8662259, 2, [(2, 1), (11, 1), (393739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_393739
  · decide +kernel

theorem prime_10373249 : Nat.Prime 10373249 := by
  apply nodeValid_prime [2, 81041] ⟨10373249, 3, [(2, 7), (81041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_81041
  · decide +kernel

theorem prime_10590347 : Nat.Prime 10590347 := by
  apply nodeValid_prime [2, 13, 407321] ⟨10590347, 2, [(2, 1), (13, 1), (407321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_407321
  · decide +kernel

theorem prime_12550547 : Nat.Prime 12550547 := by
  apply nodeValid_prime [2, 6275273] ⟨12550547, 2, [(2, 1), (6275273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6275273
  · decide +kernel

theorem prime_12839501 : Nat.Prime 12839501 := by
  apply nodeValid_prime [2, 5, 25679] ⟨12839501, 2, [(2, 2), (5, 3), (25679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25679
  · decide +kernel

theorem prime_13579933 : Nat.Prime 13579933 := by
  apply nodeValid_prime [2, 3, 103, 10987] ⟨13579933, 2, [(2, 2), (3, 1), (103, 1), (10987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_10987
  · decide +kernel

theorem prime_17797519 : Nat.Prime 17797519 := by
  apply nodeValid_prime [2, 3, 37, 26723] ⟨17797519, 3, [(2, 1), (3, 2), (37, 1), (26723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_26723
  · decide +kernel

theorem prime_18864971 : Nat.Prime 18864971 := by
  apply nodeValid_prime [2, 5, 269, 7013] ⟨18864971, 2, [(2, 1), (5, 1), (269, 1), (7013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_7013
  · decide +kernel

theorem prime_21851057 : Nat.Prime 21851057 := by
  apply nodeValid_prime [2, 251, 5441] ⟨21851057, 3, [(2, 4), (251, 1), (5441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_5441
  · decide +kernel

theorem prime_21949663 : Nat.Prime 21949663 := by
  apply nodeValid_prime [2, 3, 7, 151, 3461] ⟨21949663, 3, [(2, 1), (3, 1), (7, 1), (151, 1), (3461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
    · exact prime_3461
  · decide +kernel

theorem prime_37729943 : Nat.Prime 37729943 := by
  apply nodeValid_prime [2, 18864971] ⟨37729943, 5, [(2, 1), (18864971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18864971
  · decide +kernel

theorem prime_42015487 : Nat.Prime 42015487 := by
  apply nodeValid_prime [2, 3, 7002581] ⟨42015487, 3, [(2, 1), (3, 1), (7002581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7002581
  · decide +kernel

theorem prime_42298631 : Nat.Prime 42298631 := by
  apply nodeValid_prime [2, 5, 11, 384533] ⟨42298631, 7, [(2, 1), (5, 1), (11, 1), (384533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_384533
  · decide +kernel

theorem prime_135472121 : Nat.Prime 135472121 := by
  apply nodeValid_prime [2, 5, 7, 483829] ⟨135472121, 15, [(2, 3), (5, 1), (7, 1), (483829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_483829
  · decide +kernel

theorem prime_141072917 : Nat.Prime 141072917 := by
  apply nodeValid_prime [2, 167, 211187] ⟨141072917, 2, [(2, 2), (167, 1), (211187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_211187
  · decide +kernel

theorem prime_238873861 : Nat.Prime 238873861 := by
  apply nodeValid_prime [2, 3, 5, 23, 2137] ⟨238873861, 6, [(2, 2), (3, 5), (5, 1), (23, 1), (2137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_2137
  · decide +kernel

theorem prime_246487937 : Nat.Prime 246487937 := by
  apply nodeValid_prime [2, 29, 66403] ⟨246487937, 3, [(2, 7), (29, 1), (66403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_66403
  · decide +kernel

theorem prime_260469431 : Nat.Prime 260469431 := by
  apply nodeValid_prime [2, 5, 13, 2003611] ⟨260469431, 53, [(2, 1), (5, 1), (13, 1), (2003611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2003611
  · decide +kernel

theorem prime_361218133 : Nat.Prime 361218133 := by
  apply nodeValid_prime [2, 3, 11, 912167] ⟨361218133, 2, [(2, 2), (3, 2), (11, 1), (912167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_912167
  · decide +kernel

theorem prime_437653841 : Nat.Prime 437653841 := by
  apply nodeValid_prime [2, 5, 13, 283, 1487] ⟨437653841, 3, [(2, 4), (5, 1), (13, 1), (283, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_283
    · exact prime_1487
  · decide +kernel

theorem prime_748848911 : Nat.Prime 748848911 := by
  apply nodeValid_prime [2, 5, 5683, 13177] ⟨748848911, 19, [(2, 1), (5, 1), (5683, 1), (13177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5683
    · exact prime_13177
  · decide +kernel

theorem prime_938749597 : Nat.Prime 938749597 := by
  apply nodeValid_prime [2, 3, 67, 1167599] ⟨938749597, 2, [(2, 2), (3, 1), (67, 1), (1167599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1167599
  · decide +kernel

theorem prime_1067234183 : Nat.Prime 1067234183 := by
  apply nodeValid_prime [2, 7, 41, 53, 35081] ⟨1067234183, 5, [(2, 1), (7, 1), (41, 1), (53, 1), (35081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_53
    · exact prime_35081
  · decide +kernel

theorem prime_1982007899 : Nat.Prime 1982007899 := by
  apply nodeValid_prime [2, 13, 1201, 63473] ⟨1982007899, 2, [(2, 1), (13, 1), (1201, 1), (63473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1201
    · exact prime_63473
  · decide +kernel

theorem prime_2154166303 : Nat.Prime 2154166303 := by
  apply nodeValid_prime [2, 3, 151, 1361, 1747] ⟨2154166303, 5, [(2, 1), (3, 1), (151, 1), (1361, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_1361
    · exact prime_1747
  · decide +kernel

theorem prime_2700290323 : Nat.Prime 2700290323 := by
  apply nodeValid_prime [2, 3, 53, 317, 8929] ⟨2700290323, 2, [(2, 1), (3, 2), (53, 1), (317, 1), (8929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_317
    · exact prime_8929
  · decide +kernel

theorem prime_2847603041 : Nat.Prime 2847603041 := by
  apply nodeValid_prime [2, 5, 17797519] ⟨2847603041, 3, [(2, 5), (5, 1), (17797519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17797519
  · decide +kernel

theorem prime_3072271421 : Nat.Prime 3072271421 := by
  apply nodeValid_prime [2, 5, 8837, 17383] ⟨3072271421, 2, [(2, 2), (5, 1), (8837, 1), (17383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8837
    · exact prime_17383
  · decide +kernel

theorem prime_3305093023 : Nat.Prime 3305093023 := by
  apply nodeValid_prime [2, 3, 7, 11, 340661] ⟨3305093023, 5, [(2, 1), (3, 2), (7, 2), (11, 1), (340661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_340661
  · decide +kernel

theorem prime_4581865697 : Nat.Prime 4581865697 := by
  apply nodeValid_prime [2, 23, 37, 168253] ⟨4581865697, 3, [(2, 5), (23, 1), (37, 1), (168253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_168253
  · decide +kernel

theorem prime_5539316551 : Nat.Prime 5539316551 := by
  apply nodeValid_prime [2, 3, 5, 17, 23, 94447] ⟨5539316551, 3, [(2, 1), (3, 1), (5, 2), (17, 1), (23, 1), (94447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_94447
  · decide +kernel

theorem prime_6293104417 : Nat.Prime 6293104417 := by
  apply nodeValid_prime [2, 3, 21851057] ⟨6293104417, 5, [(2, 5), (3, 2), (21851057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21851057
  · decide +kernel

theorem prime_6427222601 : Nat.Prime 6427222601 := by
  apply nodeValid_prime [2, 5, 953, 33721] ⟨6427222601, 3, [(2, 3), (5, 2), (953, 1), (33721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_953
    · exact prime_33721
  · decide +kernel

theorem prime_8091134221 : Nat.Prime 8091134221 := by
  apply nodeValid_prime [2, 3, 5, 13, 10373249] ⟨8091134221, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (10373249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_10373249
  · decide +kernel

theorem prime_12181547393 : Nat.Prime 12181547393 := by
  apply nodeValid_prime [2, 7, 41, 127, 373] ⟨12181547393, 5, [(2, 7), (7, 2), (41, 1), (127, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_127
    · exact prime_373
  · decide +kernel

theorem prime_12204012629 : Nat.Prime 12204012629 := by
  apply nodeValid_prime [2, 139, 21949663] ⟨12204012629, 2, [(2, 2), (139, 1), (21949663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_21949663
  · decide +kernel

theorem prime_12854445203 : Nat.Prime 12854445203 := by
  apply nodeValid_prime [2, 6427222601] ⟨12854445203, 2, [(2, 1), (6427222601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6427222601
  · decide +kernel

theorem prime_23916854483 : Nat.Prime 23916854483 := by
  apply nodeValid_prime [2, 18719, 638839] ⟨23916854483, 2, [(2, 1), (18719, 1), (638839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18719
    · exact prime_638839
  · decide +kernel

theorem prime_24363094739 : Nat.Prime 24363094739 := by
  apply nodeValid_prime [2, 257, 521, 90977] ⟨24363094739, 2, [(2, 1), (257, 1), (521, 1), (90977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_521
    · exact prime_90977
  · decide +kernel

theorem prime_24363094787 : Nat.Prime 24363094787 := by
  apply nodeValid_prime [2, 12181547393] ⟨24363094787, 2, [(2, 1), (12181547393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12181547393
  · decide +kernel

theorem prime_24408025259 : Nat.Prime 24408025259 := by
  apply nodeValid_prime [2, 12204012629] ⟨24408025259, 2, [(2, 1), (12204012629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12204012629
  · decide +kernel

theorem prime_28162487911 : Nat.Prime 28162487911 := by
  apply nodeValid_prime [2, 3, 5, 938749597] ⟨28162487911, 6, [(2, 1), (3, 1), (5, 1), (938749597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_938749597
  · decide +kernel

theorem prime_33112508281 : Nat.Prime 33112508281 := by
  apply nodeValid_prime [2, 3, 5, 743, 371383] ⟨33112508281, 7, [(2, 3), (3, 1), (5, 1), (743, 1), (371383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_743
    · exact prime_371383
  · decide +kernel

theorem prime_33857500081 : Nat.Prime 33857500081 := by
  apply nodeValid_prime [2, 3, 5, 141072917] ⟨33857500081, 7, [(2, 4), (3, 1), (5, 1), (141072917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_141072917
  · decide +kernel

theorem prime_55290270527 : Nat.Prime 55290270527 := by
  apply nodeValid_prime [2, 18229, 1516547] ⟨55290270527, 5, [(2, 1), (18229, 1), (1516547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18229
    · exact prime_1516547
  · decide +kernel

theorem prime_56952060821 : Nat.Prime 56952060821 := by
  apply nodeValid_prime [2, 5, 2847603041] ⟨56952060821, 3, [(2, 2), (5, 1), (2847603041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2847603041
  · decide +kernel

theorem prime_82473582547 : Nat.Prime 82473582547 := by
  apply nodeValid_prime [2, 3, 4581865697] ⟨82473582547, 11, [(2, 1), (3, 2), (4581865697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4581865697
  · decide +kernel

theorem prime_84643750657 : Nat.Prime 84643750657 := by
  apply nodeValid_prime [2, 3, 23, 59159] ⟨84643750657, 5, [(2, 8), (3, 5), (23, 1), (59159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_59159
  · decide +kernel

theorem prime_166179496979 : Nat.Prime 166179496979 := by
  apply nodeValid_prime [2, 11, 29, 260469431] ⟨166179496979, 2, [(2, 1), (11, 1), (29, 1), (260469431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_260469431
  · decide +kernel

theorem prime_168662790899 : Nat.Prime 168662790899 := by
  apply nodeValid_prime [2, 7, 43, 4099, 68351] ⟨168662790899, 2, [(2, 1), (7, 1), (43, 1), (4099, 1), (68351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_4099
    · exact prime_68351
  · decide +kernel

theorem prime_168974938823 : Nat.Prime 168974938823 := by
  apply nodeValid_prime [2, 587, 5011, 28723] ⟨168974938823, 5, [(2, 1), (587, 1), (5011, 1), (28723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_587
    · exact prime_5011
    · exact prime_28723
  · decide +kernel

theorem prime_172118208683 : Nat.Prime 172118208683 := by
  apply nodeValid_prime [2, 7, 81919, 150077] ⟨172118208683, 5, [(2, 1), (7, 1), (81919, 1), (150077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_81919
    · exact prime_150077
  · decide +kernel

theorem prime_329894293303 : Nat.Prime 329894293303 := by
  apply nodeValid_prime [2, 3, 7, 1291, 289721] ⟨329894293303, 19, [(2, 1), (3, 2), (7, 2), (1291, 1), (289721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1291
    · exact prime_289721
  · decide +kernel

theorem prime_329894330189 : Nat.Prime 329894330189 := by
  apply nodeValid_prime [2, 82473582547] ⟨329894330189, 2, [(2, 2), (82473582547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82473582547
  · decide +kernel

theorem prime_330509302301 : Nat.Prime 330509302301 := by
  apply nodeValid_prime [2, 5, 3305093023] ⟨330509302301, 2, [(2, 2), (5, 2), (3305093023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3305093023
  · decide +kernel

theorem prime_330509302309 : Nat.Prime 330509302309 := by
  apply nodeValid_prime [2, 3, 88883, 103291] ⟨330509302309, 2, [(2, 2), (3, 2), (88883, 1), (103291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_88883
    · exact prime_103291
  · decide +kernel

theorem prime_330509319337 : Nat.Prime 330509319337 := by
  apply nodeValid_prime [2, 3, 7, 83, 7900873] ⟨330509319337, 5, [(2, 3), (3, 2), (7, 1), (83, 1), (7900873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_7900873
  · decide +kernel

theorem prime_331125082811 : Nat.Prime 331125082811 := by
  apply nodeValid_prime [2, 5, 33112508281] ⟨331125082811, 2, [(2, 1), (5, 1), (33112508281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33112508281
  · decide +kernel

theorem prime_331125087779 : Nat.Prime 331125087779 := by
  apply nodeValid_prime [2, 109, 229, 6632849] ⟨331125087779, 2, [(2, 1), (109, 1), (229, 1), (6632849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_229
    · exact prime_6632849
  · decide +kernel

theorem prime_331125088109 : Nat.Prime 331125088109 := by
  apply nodeValid_prime [2, 133051, 622177] ⟨331125088109, 2, [(2, 2), (133051, 1), (622177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_133051
    · exact prime_622177
  · decide +kernel

theorem prime_331741610663 : Nat.Prime 331741610663 := by
  apply nodeValid_prime [2, 7, 11, 2154166303] ⟨331741610663, 5, [(2, 1), (7, 1), (11, 1), (2154166303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_2154166303
  · decide +kernel

theorem prime_331741611479 : Nat.Prime 331741611479 := by
  apply nodeValid_prime [2, 379, 437653841] ⟨331741611479, 11, [(2, 1), (379, 1), (437653841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_437653841
  · decide +kernel

theorem prime_331741623163 : Nat.Prime 331741623163 := by
  apply nodeValid_prime [2, 3, 55290270527] ⟨331741623163, 3, [(2, 1), (3, 1), (55290270527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55290270527
  · decide +kernel

theorem prime_332358944473 : Nat.Prime 332358944473 := by
  apply nodeValid_prime [2, 3, 25999, 59183] ⟨332358944473, 5, [(2, 3), (3, 3), (25999, 1), (59183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25999
    · exact prime_59183
  · decide +kernel

theorem prime_332358993061 : Nat.Prime 332358993061 := by
  apply nodeValid_prime [2, 3, 5, 5539316551] ⟨332358993061, 2, [(2, 2), (3, 1), (5, 1), (5539316551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5539316551
  · decide +kernel

theorem prime_332358993959 : Nat.Prime 332358993959 := by
  apply nodeValid_prime [2, 166179496979] ⟨332358993959, 11, [(2, 1), (166179496979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_166179496979
  · decide +kernel

theorem prime_332977038509 : Nat.Prime 332977038509 := by
  apply nodeValid_prime [2, 701, 3359, 35353] ⟨332977038509, 2, [(2, 2), (701, 1), (3359, 1), (35353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_701
    · exact prime_3359
    · exact prime_35353
  · decide +kernel

theorem prime_332977065023 : Nat.Prime 332977065023 := by
  apply nodeValid_prime [2, 7, 128969, 184417] ⟨332977065023, 5, [(2, 1), (7, 1), (128969, 1), (184417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_128969
    · exact prime_184417
  · decide +kernel

theorem prime_332977065097 : Nat.Prime 332977065097 := by
  apply nodeValid_prime [2, 3, 13, 1067234183] ⟨332977065097, 10, [(2, 3), (3, 1), (13, 1), (1067234183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1067234183
  · decide +kernel

theorem prime_333595914983 : Nat.Prime 333595914983 := by
  apply nodeValid_prime [2, 11, 1181, 12839501] ⟨333595914983, 5, [(2, 1), (11, 1), (1181, 1), (12839501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1181
    · exact prime_12839501
  · decide +kernel

theorem prime_333595929851 : Nat.Prime 333595929851 := by
  apply nodeValid_prime [2, 5, 17257, 386621] ⟨333595929851, 6, [(2, 1), (5, 2), (17257, 1), (386621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17257
    · exact prime_386621
  · decide +kernel

theorem prime_333595930501 : Nat.Prime 333595930501 := by
  apply nodeValid_prime [2, 3, 5, 7, 10590347] ⟨333595930501, 2, [(2, 2), (3, 2), (5, 3), (7, 1), (10590347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_10590347
  · decide +kernel

theorem prime_334215568789 : Nat.Prime 334215568789 := by
  apply nodeValid_prime [2, 3, 257, 433, 250279] ⟨334215568789, 2, [(2, 2), (3, 1), (257, 1), (433, 1), (250279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_433
    · exact prime_250279
  · decide +kernel

theorem prime_334215574991 : Nat.Prime 334215574991 := by
  apply nodeValid_prime [2, 5, 11, 41, 6736859] ⟨334215574991, 7, [(2, 1), (5, 1), (11, 2), (41, 1), (6736859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_6736859
  · decide +kernel

theorem prime_334215575279 : Nat.Prime 334215575279 := by
  apply nodeValid_prime [2, 13, 12854445203] ⟨334215575279, 11, [(2, 1), (13, 1), (12854445203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_12854445203
  · decide +kernel

theorem prime_334835962763 : Nat.Prime 334835962763 := by
  apply nodeValid_prime [2, 7, 23916854483] ⟨334835962763, 2, [(2, 1), (7, 1), (23916854483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23916854483
  · decide +kernel

theorem prime_334835962997 : Nat.Prime 334835962997 := by
  apply nodeValid_prime [2, 1979, 42298631] ⟨334835962997, 2, [(2, 2), (1979, 1), (42298631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1979
    · exact prime_42298631
  · decide +kernel

theorem prime_334836000053 : Nat.Prime 334836000053 := by
  apply nodeValid_prime [2, 31, 2700290323] ⟨334836000053, 2, [(2, 2), (31, 1), (2700290323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2700290323
  · decide +kernel

theorem prime_335457211351 : Nat.Prime 335457211351 := by
  apply nodeValid_prime [2, 3, 5, 67, 89, 375043] ⟨335457211351, 3, [(2, 1), (3, 1), (5, 2), (67, 1), (89, 1), (375043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_89
    · exact prime_375043
  · decide +kernel

theorem prime_335457255083 : Nat.Prime 335457255083 := by
  apply nodeValid_prime [2, 47, 197, 1297, 13967] ⟨335457255083, 2, [(2, 1), (47, 1), (197, 1), (1297, 1), (13967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_197
    · exact prime_1297
    · exact prime_13967
  · decide +kernel

theorem prime_335457255299 : Nat.Prime 335457255299 := by
  apply nodeValid_prime [2, 11, 29, 2161, 243311] ⟨335457255299, 2, [(2, 1), (11, 1), (29, 1), (2161, 1), (243311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_2161
    · exact prime_243311
  · decide +kernel

theorem prime_336079202903 : Nat.Prime 336079202903 := by
  apply nodeValid_prime [2, 67, 8681, 288913] ⟨336079202903, 5, [(2, 1), (67, 1), (8681, 1), (288913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_8681
    · exact prime_288913
  · decide +kernel

theorem prime_336079204289 : Nat.Prime 336079204289 := by
  apply nodeValid_prime [2, 103, 257, 198377] ⟨336079204289, 3, [(2, 6), (103, 1), (257, 1), (198377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_257
    · exact prime_198377
  · decide +kernel

theorem prime_336701978101 : Nat.Prime 336701978101 := by
  apply nodeValid_prime [2, 3, 5, 3323, 112583] ⟨336701978101, 2, [(2, 2), (3, 2), (5, 2), (3323, 1), (112583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3323
    · exact prime_112583
  · decide +kernel

theorem prime_336702007331 : Nat.Prime 336702007331 := by
  apply nodeValid_prime [2, 5, 13, 23, 8662259] ⟨336702007331, 2, [(2, 1), (5, 1), (13, 2), (23, 1), (8662259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_8662259
  · decide +kernel

theorem prime_336702011333 : Nat.Prime 336702011333 := by
  apply nodeValid_prime [2, 23, 97, 37729943] ⟨336702011333, 2, [(2, 2), (23, 1), (97, 1), (37729943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_97
    · exact prime_37729943
  · decide +kernel

theorem prime_337325535721 : Nat.Prime 337325535721 := by
  apply nodeValid_prime [2, 3, 5, 23, 13579933] ⟨337325535721, 13, [(2, 3), (3, 3), (5, 1), (23, 1), (13579933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_13579933
  · decide +kernel

theorem prime_337325581291 : Nat.Prime 337325581291 := by
  apply nodeValid_prime [2, 3, 5, 83, 135472121] ⟨337325581291, 2, [(2, 1), (3, 1), (5, 1), (83, 1), (135472121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_135472121
  · decide +kernel

theorem prime_337325581799 : Nat.Prime 337325581799 := by
  apply nodeValid_prime [2, 168662790899] ⟨337325581799, 13, [(2, 1), (168662790899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_168662790899
  · decide +kernel

theorem prime_337949854933 : Nat.Prime 337949854933 := by
  apply nodeValid_prime [2, 3, 28162487911] ⟨337949854933, 6, [(2, 2), (3, 1), (28162487911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28162487911
  · decide +kernel

theorem prime_337949856311 : Nat.Prime 337949856311 := by
  apply nodeValid_prime [2, 5, 11, 3072271421] ⟨337949856311, 7, [(2, 1), (5, 1), (11, 1), (3072271421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3072271421
  · decide +kernel

theorem prime_337949877647 : Nat.Prime 337949877647 := by
  apply nodeValid_prime [2, 168974938823] ⟨337949877647, 5, [(2, 1), (168974938823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_168974938823
  · decide +kernel

theorem prime_338575000811 : Nat.Prime 338575000811 := by
  apply nodeValid_prime [2, 5, 33857500081] ⟨338575000811, 2, [(2, 1), (5, 1), (33857500081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33857500081
  · decide +kernel

theorem prime_338575002629 : Nat.Prime 338575002629 := by
  apply nodeValid_prime [2, 84643750657] ⟨338575002629, 2, [(2, 2), (84643750657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84643750657
  · decide +kernel

theorem prime_338575002679 : Nat.Prime 338575002679 := by
  apply nodeValid_prime [2, 3, 11, 1663, 31159] ⟨338575002679, 3, [(2, 1), (3, 3), (11, 2), (1663, 1), (31159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1663
    · exact prime_31159
  · decide +kernel

theorem prime_339200881583 : Nat.Prime 339200881583 := by
  apply nodeValid_prime [2, 19, 31, 761, 378379] ⟨339200881583, 5, [(2, 1), (19, 1), (31, 1), (761, 1), (378379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_761
    · exact prime_378379
  · decide +kernel

theorem prime_339200882621 : Nat.Prime 339200882621 := by
  apply nodeValid_prime [2, 5, 71, 238873861] ⟨339200882621, 3, [(2, 2), (5, 1), (71, 1), (238873861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_238873861
  · decide +kernel

theorem prime_339200908661 : Nat.Prime 339200908661 := by
  apply nodeValid_prime [2, 5, 499, 3313, 10259] ⟨339200908661, 2, [(2, 2), (5, 1), (499, 1), (3313, 1), (10259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_499
    · exact prime_3313
    · exact prime_10259
  · decide +kernel

theorem prime_339827596819 : Nat.Prime 339827596819 := by
  apply nodeValid_prime [2, 3, 20411, 2774873] ⟨339827596819, 3, [(2, 1), (3, 1), (20411, 1), (2774873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20411
    · exact prime_2774873
  · decide +kernel

theorem prime_339827637283 : Nat.Prime 339827637283 := by
  apply nodeValid_prime [2, 3, 7, 8091134221] ⟨339827637283, 2, [(2, 1), (3, 1), (7, 1), (8091134221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8091134221
  · decide +kernel

theorem prime_339827638519 : Nat.Prime 339827638519 := by
  apply nodeValid_prime [2, 3, 6293104417] ⟨339827638519, 6, [(2, 1), (3, 3), (6293104417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6293104417
  · decide +kernel

theorem prime_340455058483 : Nat.Prime 340455058483 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 6192569] ⟨340455058483, 2, [(2, 1), (3, 1), (7, 2), (11, 1), (17, 1), (6192569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_6192569
  · decide +kernel

theorem prime_340455070997 : Nat.Prime 340455070997 := by
  apply nodeValid_prime [2, 641, 2473, 53693] ⟨340455070997, 2, [(2, 2), (641, 1), (2473, 1), (53693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_2473
    · exact prime_53693
  · decide +kernel

theorem prime_341083326347 : Nat.Prime 341083326347 := by
  apply nodeValid_prime [2, 7, 24363094739] ⟨341083326347, 2, [(2, 1), (7, 1), (24363094739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_24363094739
  · decide +kernel

theorem prime_341083326901 : Nat.Prime 341083326901 := by
  apply nodeValid_prime [2, 3, 5, 547, 2078509] ⟨341083326901, 6, [(2, 2), (3, 1), (5, 2), (547, 1), (2078509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_547
    · exact prime_2078509
  · decide +kernel

theorem prime_341083327019 : Nat.Prime 341083327019 := by
  apply nodeValid_prime [2, 7, 24363094787] ⟨341083327019, 2, [(2, 1), (7, 1), (24363094787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_24363094787
  · decide +kernel

theorem prime_341712353627 : Nat.Prime 341712353627 := by
  apply nodeValid_prime [2, 7, 24408025259] ⟨341712353627, 2, [(2, 1), (7, 1), (24408025259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_24408025259
  · decide +kernel

theorem prime_341712353819 : Nat.Prime 341712353819 := by
  apply nodeValid_prime [2, 11, 43, 361218133] ⟨341712353819, 2, [(2, 1), (11, 1), (43, 1), (361218133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_361218133
  · decide +kernel

theorem prime_341712364927 : Nat.Prime 341712364927 := by
  apply nodeValid_prime [2, 3, 56952060821] ⟨341712364927, 3, [(2, 1), (3, 1), (56952060821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56952060821
  · decide +kernel

theorem prime_342342186331 : Nat.Prime 342342186331 := by
  apply nodeValid_prime [2, 3, 5, 97, 349, 521, 647] ⟨342342186331, 2, [(2, 1), (3, 1), (5, 1), (97, 1), (349, 1), (521, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_349
    · exact prime_521
    · exact prime_647
  · decide +kernel

theorem prime_342342186691 : Nat.Prime 342342186691 := by
  apply nodeValid_prime [2, 3, 5, 7, 8543, 190823] ⟨342342186691, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (8543, 1), (190823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_8543
    · exact prime_190823
  · decide +kernel

theorem prime_342342188077 : Nat.Prime 342342188077 := by
  apply nodeValid_prime [2, 3, 7, 97, 42015487] ⟨342342188077, 2, [(2, 2), (3, 1), (7, 1), (97, 1), (42015487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_42015487
  · decide +kernel

theorem prime_342972801239 : Nat.Prime 342972801239 := by
  apply nodeValid_prime [2, 229, 748848911] ⟨342972801239, 19, [(2, 1), (229, 1), (748848911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_748848911
  · decide +kernel

theorem prime_342972804821 : Nat.Prime 342972804821 := by
  apply nodeValid_prime [2, 5, 43, 307, 1299041] ⟨342972804821, 2, [(2, 2), (5, 1), (43, 1), (307, 1), (1299041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_307
    · exact prime_1299041
  · decide +kernel

theorem prime_342972805033 : Nat.Prime 342972805033 := by
  apply nodeValid_prime [2, 3, 11, 13, 31, 97687] ⟨342972805033, 5, [(2, 3), (3, 2), (11, 2), (13, 1), (31, 1), (97687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_97687
  · decide +kernel

theorem prime_343604184179 : Nat.Prime 343604184179 := by
  apply nodeValid_prime [2, 17, 41, 246487937] ⟨343604184179, 2, [(2, 1), (17, 1), (41, 1), (246487937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_246487937
  · decide +kernel

theorem prime_343604184401 : Nat.Prime 343604184401 := by
  apply nodeValid_prime [2, 5, 151, 5688811] ⟨343604184401, 3, [(2, 4), (5, 2), (151, 1), (5688811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_5688811
  · decide +kernel

theorem prime_343604207627 : Nat.Prime 343604207627 := by
  apply nodeValid_prime [2, 89, 193, 911, 10979] ⟨343604207627, 2, [(2, 1), (89, 1), (193, 1), (911, 1), (10979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_193
    · exact prime_911
    · exact prime_10979
  · decide +kernel

theorem prime_344236403117 : Nat.Prime 344236403117 := by
  apply nodeValid_prime [2, 6857, 12550547] ⟨344236403117, 2, [(2, 2), (6857, 1), (12550547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6857
    · exact prime_12550547
  · decide +kernel

theorem prime_344236416617 : Nat.Prime 344236416617 := by
  apply nodeValid_prime [2, 31, 1061, 1308247] ⟨344236416617, 3, [(2, 3), (31, 1), (1061, 1), (1308247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1061
    · exact prime_1308247
  · decide +kernel

theorem prime_344236417367 : Nat.Prime 344236417367 := by
  apply nodeValid_prime [2, 172118208683] ⟨344236417367, 5, [(2, 1), (172118208683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_172118208683
  · decide +kernel

theorem prime_344869373921 : Nat.Prime 344869373921 := by
  apply nodeValid_prime [2, 5, 17, 19, 6673169] ⟨344869373921, 3, [(2, 5), (5, 1), (17, 1), (19, 1), (6673169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_6673169
  · decide +kernel

theorem prime_344869374427 : Nat.Prime 344869374427 := by
  apply nodeValid_prime [2, 3, 29, 1982007899] ⟨344869374427, 2, [(2, 1), (3, 1), (29, 1), (1982007899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1982007899
  · decide +kernel

theorem prime_344869384711 : Nat.Prime 344869384711 := by
  apply nodeValid_prime [2, 3, 5, 151, 2791, 27277] ⟨344869384711, 6, [(2, 1), (3, 1), (5, 1), (151, 1), (2791, 1), (27277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_2791
    · exact prime_27277
  · decide +kernel

end Sude.Lucas.Generated
