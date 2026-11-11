import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0095

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10939 : Nat.Prime 10939 := by
  apply nodeValid_prime [2, 3, 1823] ⟨10939, 3, [(2, 1), (3, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1823
  · decide +kernel

theorem prime_11821 : Nat.Prime 11821 := by
  apply nodeValid_prime [2, 3, 5, 197] ⟨11821, 2, [(2, 2), (3, 1), (5, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
  · decide +kernel

theorem prime_17029 : Nat.Prime 17029 := by
  apply nodeValid_prime [2, 3, 11, 43] ⟨17029, 10, [(2, 2), (3, 2), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_17657 : Nat.Prime 17657 := by
  apply nodeValid_prime [2, 2207] ⟨17657, 3, [(2, 3), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2207
  · decide +kernel

theorem prime_20233 : Nat.Prime 20233 := by
  apply nodeValid_prime [2, 3, 281] ⟨20233, 5, [(2, 3), (3, 2), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
  · decide +kernel

theorem prime_21683 : Nat.Prime 21683 := by
  apply nodeValid_prime [2, 37, 293] ⟨21683, 2, [(2, 1), (37, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_293
  · decide +kernel

theorem prime_27919 : Nat.Prime 27919 := by
  apply nodeValid_prime [2, 3, 11, 47] ⟨27919, 3, [(2, 1), (3, 3), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_32141 : Nat.Prime 32141 := by
  apply nodeValid_prime [2, 5, 1607] ⟨32141, 2, [(2, 2), (5, 1), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1607
  · decide +kernel

theorem prime_32839 : Nat.Prime 32839 := by
  apply nodeValid_prime [2, 3, 13, 421] ⟨32839, 6, [(2, 1), (3, 1), (13, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_421
  · decide +kernel

theorem prime_37123 : Nat.Prime 37123 := by
  apply nodeValid_prime [2, 3, 23, 269] ⟨37123, 3, [(2, 1), (3, 1), (23, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_269
  · decide +kernel

theorem prime_37693 : Nat.Prime 37693 := by
  apply nodeValid_prime [2, 3, 349] ⟨37693, 2, [(2, 2), (3, 3), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
  · decide +kernel

theorem prime_38543 : Nat.Prime 38543 := by
  apply nodeValid_prime [2, 7, 2753] ⟨38543, 5, [(2, 1), (7, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2753
  · decide +kernel

theorem prime_41903 : Nat.Prime 41903 := by
  apply nodeValid_prime [2, 7, 41, 73] ⟨41903, 5, [(2, 1), (7, 1), (41, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_73
  · decide +kernel

theorem prime_47161 : Nat.Prime 47161 := by
  apply nodeValid_prime [2, 3, 5, 131] ⟨47161, 17, [(2, 3), (3, 2), (5, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
  · decide +kernel

theorem prime_53269 : Nat.Prime 53269 := by
  apply nodeValid_prime [2, 3, 23, 193] ⟨53269, 7, [(2, 2), (3, 1), (23, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_193
  · decide +kernel

theorem prime_61627 : Nat.Prime 61627 := by
  apply nodeValid_prime [2, 3, 10271] ⟨61627, 3, [(2, 1), (3, 1), (10271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10271
  · decide +kernel

theorem prime_62791 : Nat.Prime 62791 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 23] ⟨62791, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_66221 : Nat.Prime 66221 := by
  apply nodeValid_prime [2, 5, 7, 11, 43] ⟨66221, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_85513 : Nat.Prime 85513 := by
  apply nodeValid_prime [2, 3, 7, 509] ⟨85513, 5, [(2, 3), (3, 1), (7, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_509
  · decide +kernel

theorem prime_85669 : Nat.Prime 85669 := by
  apply nodeValid_prime [2, 3, 11, 59] ⟨85669, 2, [(2, 2), (3, 1), (11, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_90073 : Nat.Prime 90073 := by
  apply nodeValid_prime [2, 3, 139] ⟨90073, 10, [(2, 3), (3, 4), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_94109 : Nat.Prime 94109 := by
  apply nodeValid_prime [2, 7, 3361] ⟨94109, 2, [(2, 2), (7, 1), (3361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3361
  · decide +kernel

theorem prime_97213 : Nat.Prime 97213 := by
  apply nodeValid_prime [2, 3, 8101] ⟨97213, 5, [(2, 2), (3, 1), (8101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8101
  · decide +kernel

theorem prime_101719 : Nat.Prime 101719 := by
  apply nodeValid_prime [2, 3, 5651] ⟨101719, 3, [(2, 1), (3, 2), (5651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5651
  · decide +kernel

theorem prime_126949 : Nat.Prime 126949 := by
  apply nodeValid_prime [2, 3, 71, 149] ⟨126949, 2, [(2, 2), (3, 1), (71, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_149
  · decide +kernel

theorem prime_162527 : Nat.Prime 162527 := by
  apply nodeValid_prime [2, 7, 13, 19, 47] ⟨162527, 5, [(2, 1), (7, 1), (13, 1), (19, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_170141 : Nat.Prime 170141 := by
  apply nodeValid_prime [2, 5, 47, 181] ⟨170141, 2, [(2, 2), (5, 1), (47, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_181
  · decide +kernel

theorem prime_191143 : Nat.Prime 191143 := by
  apply nodeValid_prime [2, 3, 7, 37, 41] ⟨191143, 3, [(2, 1), (3, 2), (7, 1), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_206779 : Nat.Prime 206779 := by
  apply nodeValid_prime [2, 3, 11, 13, 241] ⟨206779, 11, [(2, 1), (3, 1), (11, 1), (13, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_241
  · decide +kernel

theorem prime_208609 : Nat.Prime 208609 := by
  apply nodeValid_prime [2, 3, 41, 53] ⟨208609, 13, [(2, 5), (3, 1), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_215197 : Nat.Prime 215197 := by
  apply nodeValid_prime [2, 3, 79, 227] ⟨215197, 2, [(2, 2), (3, 1), (79, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_227
  · decide +kernel

theorem prime_220663 : Nat.Prime 220663 := by
  apply nodeValid_prime [2, 3, 13, 23, 41] ⟨220663, 5, [(2, 1), (3, 2), (13, 1), (23, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_41
  · decide +kernel

theorem prime_246509 : Nat.Prime 246509 := by
  apply nodeValid_prime [2, 61627] ⟨246509, 2, [(2, 2), (61627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61627
  · decide +kernel

theorem prime_258299 : Nat.Prime 258299 := by
  apply nodeValid_prime [2, 17, 71, 107] ⟨258299, 2, [(2, 1), (17, 1), (71, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_107
  · decide +kernel

theorem prime_340283 : Nat.Prime 340283 := by
  apply nodeValid_prime [2, 170141] ⟨340283, 2, [(2, 1), (170141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_170141
  · decide +kernel

theorem prime_392437 : Nat.Prime 392437 := by
  apply nodeValid_prime [2, 3, 11, 991] ⟨392437, 2, [(2, 2), (3, 2), (11, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_991
  · decide +kernel

theorem prime_440023 : Nat.Prime 440023 := by
  apply nodeValid_prime [2, 3, 11, 59, 113] ⟨440023, 3, [(2, 1), (3, 1), (11, 1), (59, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
    · exact prime_113
  · decide +kernel

theorem prime_583279 : Nat.Prime 583279 := by
  apply nodeValid_prime [2, 3, 97213] ⟨583279, 7, [(2, 1), (3, 1), (97213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97213
  · decide +kernel

theorem prime_599479 : Nat.Prime 599479 := by
  apply nodeValid_prime [2, 3, 11, 31, 293] ⟨599479, 6, [(2, 1), (3, 1), (11, 1), (31, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_293
  · decide +kernel

theorem prime_627911 : Nat.Prime 627911 := by
  apply nodeValid_prime [2, 5, 62791] ⟨627911, 7, [(2, 1), (5, 1), (62791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_62791
  · decide +kernel

theorem prime_671651 : Nat.Prime 671651 := by
  apply nodeValid_prime [2, 5, 7, 19, 101] ⟨671651, 19, [(2, 1), (5, 2), (7, 1), (19, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_101
  · decide +kernel

theorem prime_694763 : Nat.Prime 694763 := by
  apply nodeValid_prime [2, 383, 907] ⟨694763, 2, [(2, 1), (383, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_907
  · decide +kernel

theorem prime_710027 : Nat.Prime 710027 := by
  apply nodeValid_prime [2, 109, 3257] ⟨710027, 2, [(2, 1), (109, 1), (3257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_3257
  · decide +kernel

theorem prime_930931 : Nat.Prime 930931 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 13, 31] ⟨930931, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_1227887 : Nat.Prime 1227887 := by
  apply nodeValid_prime [2, 11, 55813] ⟨1227887, 5, [(2, 1), (11, 1), (55813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_55813
  · decide +kernel

theorem prime_1275467 : Nat.Prime 1275467 := by
  apply nodeValid_prime [2, 43, 14831] ⟨1275467, 2, [(2, 1), (43, 1), (14831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_14831
  · decide +kernel

theorem prime_1290593 : Nat.Prime 1290593 := by
  apply nodeValid_prime [2, 31, 1301] ⟨1290593, 3, [(2, 5), (31, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1301
  · decide +kernel

theorem prime_1316347 : Nat.Prime 1316347 := by
  apply nodeValid_prime [2, 3, 41, 5351] ⟨1316347, 3, [(2, 1), (3, 1), (41, 1), (5351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_5351
  · decide +kernel

theorem prime_1606009 : Nat.Prime 1606009 := by
  apply nodeValid_prime [2, 3, 61, 1097] ⟨1606009, 7, [(2, 3), (3, 1), (61, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_1097
  · decide +kernel

theorem prime_1850089 : Nat.Prime 1850089 := by
  apply nodeValid_prime [2, 3, 157, 491] ⟨1850089, 7, [(2, 3), (3, 1), (157, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_491
  · decide +kernel

theorem prime_1991489 : Nat.Prime 1991489 := by
  apply nodeValid_prime [2, 29, 37] ⟨1991489, 3, [(2, 6), (29, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_2880629 : Nat.Prime 2880629 := by
  apply nodeValid_prime [2, 19, 29, 1307] ⟨2880629, 2, [(2, 2), (19, 1), (29, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_1307
  · decide +kernel

theorem prime_3654787 : Nat.Prime 3654787 := by
  apply nodeValid_prime [2, 3, 37, 101, 163] ⟨3654787, 3, [(2, 1), (3, 1), (37, 1), (101, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_101
    · exact prime_163
  · decide +kernel

theorem prime_4168579 : Nat.Prime 4168579 := by
  apply nodeValid_prime [2, 3, 694763] ⟨4168579, 2, [(2, 1), (3, 1), (694763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_694763
  · decide +kernel

theorem prime_4177709 : Nat.Prime 4177709 := by
  apply nodeValid_prime [2, 43, 107, 227] ⟨4177709, 2, [(2, 2), (43, 1), (107, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_107
    · exact prime_227
  · decide +kernel

theorem prime_4454789 : Nat.Prime 4454789 := by
  apply nodeValid_prime [2, 13, 85669] ⟨4454789, 2, [(2, 2), (13, 1), (85669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_85669
  · decide +kernel

theorem prime_4834639 : Nat.Prime 4834639 := by
  apply nodeValid_prime [2, 3, 41, 6551] ⟨4834639, 3, [(2, 1), (3, 2), (41, 1), (6551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_6551
  · decide +kernel

theorem prime_5046049 : Nat.Prime 5046049 := by
  apply nodeValid_prime [2, 3, 7, 2503] ⟨5046049, 11, [(2, 5), (3, 2), (7, 1), (2503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2503
  · decide +kernel

theorem prime_5728049 : Nat.Prime 5728049 := by
  apply nodeValid_prime [2, 17, 21059] ⟨5728049, 3, [(2, 4), (17, 1), (21059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_21059
  · decide +kernel

theorem prime_5944819 : Nat.Prime 5944819 := by
  apply nodeValid_prime [2, 3, 11, 90073] ⟨5944819, 2, [(2, 1), (3, 1), (11, 1), (90073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_90073
  · decide +kernel

theorem prime_6429413 : Nat.Prime 6429413 := by
  apply nodeValid_prime [2, 11, 47, 3109] ⟨6429413, 3, [(2, 2), (11, 1), (47, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_3109
  · decide +kernel

theorem prime_6525193 : Nat.Prime 6525193 := by
  apply nodeValid_prime [2, 3, 23, 11821] ⟨6525193, 7, [(2, 3), (3, 1), (23, 1), (11821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_11821
  · decide +kernel

theorem prime_6529319 : Nat.Prime 6529319 := by
  apply nodeValid_prime [2, 61, 109, 491] ⟨6529319, 11, [(2, 1), (61, 1), (109, 1), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_109
    · exact prime_491
  · decide +kernel

theorem prime_6834533 : Nat.Prime 6834533 := by
  apply nodeValid_prime [2, 131, 13043] ⟨6834533, 2, [(2, 2), (131, 1), (13043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_13043
  · decide +kernel

theorem prime_7418941 : Nat.Prime 7418941 := by
  apply nodeValid_prime [2, 3, 5, 53, 2333] ⟨7418941, 2, [(2, 2), (3, 1), (5, 1), (53, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_2333
  · decide +kernel

theorem prime_8355419 : Nat.Prime 8355419 := by
  apply nodeValid_prime [2, 4177709] ⟨8355419, 2, [(2, 1), (4177709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4177709
  · decide +kernel

theorem prime_9360229 : Nat.Prime 9360229 := by
  apply nodeValid_prime [2, 3, 103, 7573] ⟨9360229, 13, [(2, 2), (3, 1), (103, 1), (7573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_7573
  · decide +kernel

theorem prime_10931489 : Nat.Prime 10931489 := by
  apply nodeValid_prime [2, 211, 1619] ⟨10931489, 3, [(2, 5), (211, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_1619
  · decide +kernel

theorem prime_11923237 : Nat.Prime 11923237 := by
  apply nodeValid_prime [2, 3, 13, 73, 349] ⟨11923237, 2, [(2, 2), (3, 2), (13, 1), (73, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_349
  · decide +kernel

theorem prime_12055447 : Nat.Prime 12055447 := by
  apply nodeValid_prime [2, 3, 13, 1321] ⟨12055447, 3, [(2, 1), (3, 3), (13, 2), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1321
  · decide +kernel

theorem prime_14255233 : Nat.Prime 14255233 := by
  apply nodeValid_prime [2, 3, 37123] ⟨14255233, 10, [(2, 7), (3, 1), (37123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37123
  · decide +kernel

theorem prime_15019973 : Nat.Prime 15019973 := by
  apply nodeValid_prime [2, 11, 31033] ⟨15019973, 2, [(2, 2), (11, 2), (31033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31033
  · decide +kernel

theorem prime_16710839 : Nat.Prime 16710839 := by
  apply nodeValid_prime [2, 8355419] ⟨16710839, 13, [(2, 1), (8355419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8355419
  · decide +kernel

theorem prime_16999207 : Nat.Prime 16999207 := by
  apply nodeValid_prime [2, 3, 7, 37, 10939] ⟨16999207, 5, [(2, 1), (3, 1), (7, 1), (37, 1), (10939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_10939
  · decide +kernel

theorem prime_21277343 : Nat.Prime 21277343 := by
  apply nodeValid_prime [2, 331, 32141] ⟨21277343, 5, [(2, 1), (331, 1), (32141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_32141
  · decide +kernel

theorem prime_26100773 : Nat.Prime 26100773 := by
  apply nodeValid_prime [2, 6525193] ⟨26100773, 2, [(2, 2), (6525193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6525193
  · decide +kernel

theorem prime_26659291 : Nat.Prime 26659291 := by
  apply nodeValid_prime [2, 3, 5, 7, 126949] ⟨26659291, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (126949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_126949
  · decide +kernel

theorem prime_35046313 : Nat.Prime 35046313 := by
  apply nodeValid_prime [2, 3, 7, 208609] ⟨35046313, 5, [(2, 3), (3, 1), (7, 1), (208609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_208609
  · decide +kernel

theorem prime_50356237 : Nat.Prime 50356237 := by
  apply nodeValid_prime [2, 3, 7, 599479] ⟨50356237, 2, [(2, 2), (3, 1), (7, 1), (599479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_599479
  · decide +kernel

theorem prime_54114509 : Nat.Prime 54114509 := by
  apply nodeValid_prime [2, 7, 19, 101719] ⟨54114509, 3, [(2, 2), (7, 1), (19, 1), (101719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_101719
  · decide +kernel

theorem prime_55440313 : Nat.Prime 55440313 := by
  apply nodeValid_prime [2, 3, 691, 3343] ⟨55440313, 5, [(2, 3), (3, 1), (691, 1), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_3343
  · decide +kernel

theorem prime_57806789 : Nat.Prime 57806789 := by
  apply nodeValid_prime [2, 13, 85513] ⟨57806789, 2, [(2, 2), (13, 2), (85513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_85513
  · decide +kernel

theorem prime_58963979 : Nat.Prime 58963979 := by
  apply nodeValid_prime [2, 137, 215197] ⟨58963979, 2, [(2, 1), (137, 1), (215197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_215197
  · decide +kernel

theorem prime_59484883 : Nat.Prime 59484883 := by
  apply nodeValid_prime [2, 3, 61, 162527] ⟨59484883, 19, [(2, 1), (3, 1), (61, 1), (162527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_162527
  · decide +kernel

theorem prime_72612619 : Nat.Prime 72612619 := by
  apply nodeValid_prime [2, 3, 13, 930931] ⟨72612619, 3, [(2, 1), (3, 1), (13, 1), (930931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_930931
  · decide +kernel

theorem prime_123520853 : Nat.Prime 123520853 := by
  apply nodeValid_prime [2, 7, 13, 61, 5563] ⟨123520853, 2, [(2, 2), (7, 1), (13, 1), (61, 1), (5563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_5563
  · decide +kernel

theorem prime_133402169 : Nat.Prime 133402169 := by
  apply nodeValid_prime [2, 37, 43, 47, 223] ⟨133402169, 3, [(2, 3), (37, 1), (43, 1), (47, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
    · exact prime_47
    · exact prime_223
  · decide +kernel

theorem prime_162015377 : Nat.Prime 162015377 := by
  apply nodeValid_prime [2, 467, 21683] ⟨162015377, 3, [(2, 4), (467, 1), (21683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_467
    · exact prime_21683
  · decide +kernel

theorem prime_285185357 : Nat.Prime 285185357 := by
  apply nodeValid_prime [2, 373, 191143] ⟨285185357, 2, [(2, 2), (373, 1), (191143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_191143
  · decide +kernel

theorem prime_356651167 : Nat.Prime 356651167 := by
  apply nodeValid_prime [2, 3, 19, 83, 37693] ⟨356651167, 3, [(2, 1), (3, 1), (19, 1), (83, 1), (37693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_83
    · exact prime_37693
  · decide +kernel

theorem prime_527986279 : Nat.Prime 527986279 := by
  apply nodeValid_prime [2, 3, 1607, 18253] ⟨527986279, 3, [(2, 1), (3, 2), (1607, 1), (18253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1607
    · exact prime_18253
  · decide +kernel

theorem prime_547711859 : Nat.Prime 547711859 := by
  apply nodeValid_prime [2, 53, 97, 53269] ⟨547711859, 2, [(2, 1), (53, 1), (97, 1), (53269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_97
    · exact prime_53269
  · decide +kernel

theorem prime_1637379199 : Nat.Prime 1637379199 := by
  apply nodeValid_prime [2, 3, 7, 13, 41, 43] ⟨1637379199, 3, [(2, 1), (3, 6), (7, 2), (13, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_2168814611 : Nat.Prime 2168814611 := by
  apply nodeValid_prime [2, 5, 17, 331, 38543] ⟨2168814611, 6, [(2, 1), (5, 1), (17, 1), (331, 1), (38543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_331
    · exact prime_38543
  · decide +kernel

theorem prime_2360800927 : Nat.Prime 2360800927 := by
  apply nodeValid_prime [2, 3, 11, 11923237] ⟨2360800927, 3, [(2, 1), (3, 2), (11, 1), (11923237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_11923237
  · decide +kernel

theorem prime_3256769251 : Nat.Prime 3256769251 := by
  apply nodeValid_prime [2, 3, 5, 7, 206779] ⟨3256769251, 3, [(2, 1), (3, 2), (5, 3), (7, 1), (206779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_206779
  · decide +kernel

theorem prime_3300116047 : Nat.Prime 3300116047 := by
  apply nodeValid_prime [2, 3, 109, 5046049] ⟨3300116047, 5, [(2, 1), (3, 1), (109, 1), (5046049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_5046049
  · decide +kernel

theorem prime_4886185099 : Nat.Prime 4886185099 := by
  apply nodeValid_prime [2, 3, 631, 1290593] ⟨4886185099, 10, [(2, 1), (3, 1), (631, 1), (1290593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
    · exact prime_1290593
  · decide +kernel

theorem prime_5275024897 : Nat.Prime 5275024897 := by
  apply nodeValid_prime [2, 3, 1031, 3331] ⟨5275024897, 5, [(2, 9), (3, 1), (1031, 1), (3331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1031
    · exact prime_3331
  · decide +kernel

theorem prime_5809413607 : Nat.Prime 5809413607 := by
  apply nodeValid_prime [2, 3, 43, 3761, 5987] ⟨5809413607, 3, [(2, 1), (3, 1), (43, 1), (3761, 1), (5987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_3761
    · exact prime_5987
  · decide +kernel

theorem prime_7997618399 : Nat.Prime 7997618399 := by
  apply nodeValid_prime [2, 7, 11, 7418941] ⟨7997618399, 7, [(2, 1), (7, 2), (11, 1), (7418941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_7418941
  · decide +kernel

theorem prime_8010072677 : Nat.Prime 8010072677 := by
  apply nodeValid_prime [2, 293, 6834533] ⟨8010072677, 2, [(2, 2), (293, 1), (6834533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_6834533
  · decide +kernel

theorem prime_11327735483 : Nat.Prime 11327735483 := by
  apply nodeValid_prime [2, 7, 31, 26100773] ⟨11327735483, 2, [(2, 1), (7, 1), (31, 1), (26100773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_26100773
  · decide +kernel

theorem prime_17292919421 : Nat.Prime 17292919421 := by
  apply nodeValid_prime [2, 5, 7, 123520853] ⟨17292919421, 2, [(2, 2), (5, 1), (7, 1), (123520853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_123520853
  · decide +kernel

theorem prime_29642166007 : Nat.Prime 29642166007 := by
  apply nodeValid_prime [2, 3, 1109, 4454789] ⟨29642166007, 3, [(2, 1), (3, 1), (1109, 1), (4454789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1109
    · exact prime_4454789
  · decide +kernel

theorem prime_29860386067 : Nat.Prime 29860386067 := by
  apply nodeValid_prime [2, 3, 7, 17, 1991489] ⟨29860386067, 2, [(2, 1), (3, 2), (7, 2), (17, 1), (1991489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_1991489
  · decide +kernel

theorem prime_30962366077 : Nat.Prime 30962366077 := by
  apply nodeValid_prime [2, 3, 181, 14255233] ⟨30962366077, 2, [(2, 2), (3, 1), (181, 1), (14255233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_14255233
  · decide +kernel

theorem prime_43831955267 : Nat.Prime 43831955267 := by
  apply nodeValid_prime [2, 11, 19, 167, 627911] ⟨43831955267, 5, [(2, 1), (11, 1), (19, 1), (167, 1), (627911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_167
    · exact prime_627911
  · decide +kernel

theorem prime_67492314497 : Nat.Prime 67492314497 := by
  apply nodeValid_prime [2, 37, 1303, 10937] ⟨67492314497, 3, [(2, 7), (37, 1), (1303, 1), (10937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1303
    · exact prime_10937
  · decide +kernel

theorem prime_78077326001 : Nat.Prime 78077326001 := by
  apply nodeValid_prime [2, 5, 37, 163, 6473] ⟨78077326001, 3, [(2, 4), (5, 3), (37, 1), (163, 1), (6473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_163
    · exact prime_6473
  · decide +kernel

theorem prime_113590238711 : Nat.Prime 113590238711 := by
  apply nodeValid_prime [2, 5, 13, 137, 2903] ⟨113590238711, 11, [(2, 1), (5, 1), (13, 4), (137, 1), (2903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_137
    · exact prime_2903
  · decide +kernel

theorem prime_212703043979 : Nat.Prime 212703043979 := by
  apply nodeValid_prime [2, 66221, 1606009] ⟨212703043979, 2, [(2, 1), (66221, 1), (1606009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_66221
    · exact prime_1606009
  · decide +kernel

theorem prime_244082227111 : Nat.Prime 244082227111 := by
  apply nodeValid_prime [2, 3, 5, 47161, 172517] ⟨244082227111, 3, [(2, 1), (3, 1), (5, 1), (47161, 1), (172517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47161
    · exact prime_172517
  · decide +kernel

theorem prime_490868531303 : Nat.Prime 490868531303 := by
  apply nodeValid_prime [2, 19, 233, 55440313] ⟨490868531303, 5, [(2, 1), (19, 1), (233, 1), (55440313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_233
    · exact prime_55440313
  · decide +kernel

theorem prime_1464493363139 : Nat.Prime 1464493363139 := by
  apply nodeValid_prime [2, 13, 6451, 671651] ⟨1464493363139, 2, [(2, 1), (13, 2), (6451, 1), (671651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_6451
    · exact prime_671651
  · decide +kernel

theorem prime_1476673050953 : Nat.Prime 1476673050953 := by
  apply nodeValid_prime [2, 11, 4483, 340283] ⟨1476673050953, 5, [(2, 3), (11, 2), (4483, 1), (340283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4483
    · exact prime_340283
  · decide +kernel

theorem prime_1493019303311 : Nat.Prime 1493019303311 := by
  apply nodeValid_prime [2, 5, 31, 89, 54114509] ⟨1493019303311, 7, [(2, 1), (5, 1), (31, 1), (89, 1), (54114509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_89
    · exact prime_54114509
  · decide +kernel

theorem prime_2926288392271 : Nat.Prime 2926288392271 := by
  apply nodeValid_prime [2, 3, 5, 17, 613, 9360229] ⟨2926288392271, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (613, 1), (9360229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_613
    · exact prime_9360229
  · decide +kernel

theorem prime_2926288392631 : Nat.Prime 2926288392631 := by
  apply nodeValid_prime [2, 3, 5, 17029, 5728049] ⟨2926288392631, 6, [(2, 1), (3, 1), (5, 1), (17029, 1), (5728049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17029
    · exact prime_5728049
  · decide +kernel

theorem prime_2926288545701 : Nat.Prime 2926288545701 := by
  apply nodeValid_prime [2, 5, 13, 31, 72612619] ⟨2926288545701, 2, [(2, 2), (5, 2), (13, 1), (31, 1), (72612619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_72612619
  · decide +kernel

theorem prime_2928986725333 : Nat.Prime 2928986725333 := by
  apply nodeValid_prime [2, 3, 244082227111] ⟨2928986725333, 5, [(2, 2), (3, 1), (244082227111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_244082227111
  · decide +kernel

theorem prime_2928986726279 : Nat.Prime 2928986726279 := by
  apply nodeValid_prime [2, 1464493363139] ⟨2928986726279, 11, [(2, 1), (1464493363139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1464493363139
  · decide +kernel

theorem prime_2931686576279 : Nat.Prime 2931686576279 := by
  apply nodeValid_prime [2, 73, 4817, 4168579] ⟨2931686576279, 13, [(2, 1), (73, 1), (4817, 1), (4168579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_4817
    · exact prime_4168579
  · decide +kernel

theorem prime_2931686579489 : Nat.Prime 2931686579489 := by
  apply nodeValid_prime [2, 29, 33569, 94109] ⟨2931686579489, 3, [(2, 5), (29, 1), (33569, 1), (94109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_33569
    · exact prime_94109
  · decide +kernel

theorem prime_2931686599783 : Nat.Prime 2931686599783 := by
  apply nodeValid_prime [2, 3, 61, 8010072677] ⟨2931686599783, 3, [(2, 1), (3, 1), (61, 1), (8010072677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_8010072677
  · decide +kernel

theorem prime_2934388160371 : Nat.Prime 2934388160371 := by
  apply nodeValid_prime [2, 3, 5, 1223, 26659291] ⟨2934388160371, 3, [(2, 1), (3, 2), (5, 1), (1223, 1), (26659291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1223
    · exact prime_26659291
  · decide +kernel

theorem prime_2934388223219 : Nat.Prime 2934388223219 := by
  apply nodeValid_prime [2, 17, 1493, 57806789] ⟨2934388223219, 2, [(2, 1), (17, 1), (1493, 1), (57806789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1493
    · exact prime_57806789
  · decide +kernel

theorem prime_2934388225169 : Nat.Prime 2934388225169 := by
  apply nodeValid_prime [2, 258299, 710027] ⟨2934388225169, 3, [(2, 4), (258299, 1), (710027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_258299
    · exact prime_710027
  · decide +kernel

theorem prime_2937091307279 : Nat.Prime 2937091307279 := by
  apply nodeValid_prime [2, 41903, 35046313] ⟨2937091307279, 41, [(2, 1), (41903, 1), (35046313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41903
    · exact prime_35046313
  · decide +kernel

theorem prime_2937091307713 : Nat.Prime 2937091307713 := by
  apply nodeValid_prime [2, 3, 179, 3061, 27919] ⟨2937091307713, 5, [(2, 6), (3, 1), (179, 1), (3061, 1), (27919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_3061
    · exact prime_27919
  · decide +kernel

theorem prime_2937091391401 : Nat.Prime 2937091391401 := by
  apply nodeValid_prime [2, 3, 5, 41, 47, 229, 11093] ⟨2937091391401, 13, [(2, 3), (3, 1), (5, 2), (41, 1), (47, 1), (229, 1), (11093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_47
    · exact prime_229
    · exact prime_11093
  · decide +kernel

theorem prime_2939796301571 : Nat.Prime 2939796301571 := by
  apply nodeValid_prime [2, 5, 17, 17292919421] ⟨2939796301571, 2, [(2, 1), (5, 1), (17, 1), (17292919421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_17292919421
  · decide +kernel

theorem prime_2939796303139 : Nat.Prime 2939796303139 := by
  apply nodeValid_prime [2, 3, 239, 1553, 440023] ⟨2939796303139, 2, [(2, 1), (3, 2), (239, 1), (1553, 1), (440023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_1553
    · exact prime_440023
  · decide +kernel

theorem prime_2942502829363 : Nat.Prime 2942502829363 := by
  apply nodeValid_prime [2, 3, 71, 5867, 392437] ⟨2942502829363, 11, [(2, 1), (3, 2), (71, 1), (5867, 1), (392437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_5867
    · exact prime_392437
  · decide +kernel

theorem prime_2942502830539 : Nat.Prime 2942502830539 := by
  apply nodeValid_prime [2, 3, 103, 317, 15019973] ⟨2942502830539, 2, [(2, 1), (3, 1), (103, 1), (317, 1), (15019973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_317
    · exact prime_15019973
  · decide +kernel

theorem prime_2942502900541 : Nat.Prime 2942502900541 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 37, 6529319] ⟨2942502900541, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (37, 1), (6529319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_37
    · exact prime_6529319
  · decide +kernel

theorem prime_2945211187819 : Nat.Prime 2945211187819 := by
  apply nodeValid_prime [2, 3, 490868531303] ⟨2945211187819, 3, [(2, 1), (3, 1), (490868531303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_490868531303
  · decide +kernel

theorem prime_2945211224693 : Nat.Prime 2945211224693 := by
  apply nodeValid_prime [2, 11, 29, 359, 6429413] ⟨2945211224693, 2, [(2, 2), (11, 1), (29, 1), (359, 1), (6429413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_359
    · exact prime_6429413
  · decide +kernel

theorem prime_2945211225581 : Nat.Prime 2945211225581 := by
  apply nodeValid_prime [2, 5, 13, 11327735483] ⟨2945211225581, 2, [(2, 2), (5, 1), (13, 1), (11327735483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_11327735483
  · decide +kernel

theorem prime_2947921130251 : Nat.Prime 2947921130251 := by
  apply nodeValid_prime [2, 3, 5, 271, 4834639] ⟨2947921130251, 2, [(2, 1), (3, 2), (5, 3), (271, 1), (4834639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
    · exact prime_4834639
  · decide +kernel

theorem prime_2947921130563 : Nat.Prime 2947921130563 := by
  apply nodeValid_prime [2, 3, 29, 127, 133402169] ⟨2947921130563, 2, [(2, 1), (3, 1), (29, 1), (127, 1), (133402169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_127
    · exact prime_133402169
  · decide +kernel

theorem prime_2947921169813 : Nat.Prime 2947921169813 := by
  apply nodeValid_prime [2, 17, 23, 32839, 57397] ⟨2947921169813, 2, [(2, 2), (17, 1), (23, 1), (32839, 1), (57397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_32839
    · exact prime_57397
  · decide +kernel

theorem prime_2950632842231 : Nat.Prime 2950632842231 := by
  apply nodeValid_prime [2, 5, 17657, 16710839] ⟨2950632842231, 14, [(2, 1), (5, 1), (17657, 1), (16710839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17657
    · exact prime_16710839
  · decide +kernel

theorem prime_2950632941407 : Nat.Prime 2950632941407 := by
  apply nodeValid_prime [2, 3, 151, 3256769251] ⟨2950632941407, 3, [(2, 1), (3, 1), (151, 1), (3256769251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_3256769251
  · decide +kernel

theorem prime_2950632942541 : Nat.Prime 2950632942541 := by
  apply nodeValid_prime [2, 3, 5, 19, 1399, 1850089] ⟨2950632942541, 10, [(2, 2), (3, 1), (5, 1), (19, 1), (1399, 1), (1850089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1399
    · exact prime_1850089
  · decide +kernel

theorem prime_2953346101907 : Nat.Prime 2953346101907 := by
  apply nodeValid_prime [2, 1476673050953] ⟨2953346101907, 2, [(2, 1), (1476673050953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1476673050953
  · decide +kernel

theorem prime_2953346102537 : Nat.Prime 2953346102537 := by
  apply nodeValid_prime [2, 947, 19267, 20233] ⟨2953346102537, 3, [(2, 3), (947, 1), (19267, 1), (20233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_947
    · exact prime_19267
    · exact prime_20233
  · decide +kernel

theorem prime_2953346206487 : Nat.Prime 2953346206487 := by
  apply nodeValid_prime [2, 13, 113590238711] ⟨2953346206487, 5, [(2, 1), (13, 1), (113590238711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113590238711
  · decide +kernel

theorem prime_2956061247751 : Nat.Prime 2956061247751 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 5944819] ⟨2956061247751, 3, [(2, 1), (3, 2), (5, 3), (13, 1), (17, 1), (5944819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_5944819
  · decide +kernel

theorem prime_2956061249131 : Nat.Prime 2956061249131 := by
  apply nodeValid_prime [2, 3, 5, 11, 283, 601, 52667] ⟨2956061249131, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (283, 1), (601, 1), (52667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_283
    · exact prime_601
    · exact prime_52667
  · decide +kernel

theorem prime_2956061262991 : Nat.Prime 2956061262991 := by
  apply nodeValid_prime [2, 3, 5, 11, 421, 21277343] ⟨2956061262991, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (421, 1), (21277343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_421
    · exact prime_21277343
  · decide +kernel

theorem prime_2958778011463 : Nat.Prime 2958778011463 := by
  apply nodeValid_prime [2, 3, 7, 13, 19, 89, 246509] ⟨2958778011463, 3, [(2, 1), (3, 1), (7, 1), (13, 2), (19, 1), (89, 1), (246509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_89
    · exact prime_246509
  · decide +kernel

theorem prime_2958778080421 : Nat.Prime 2958778080421 := by
  apply nodeValid_prime [2, 3, 5, 829, 59484883] ⟨2958778080421, 14, [(2, 2), (3, 1), (5, 1), (829, 1), (59484883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_829
    · exact prime_59484883
  · decide +kernel

theorem prime_2958778081433 : Nat.Prime 2958778081433 := by
  apply nodeValid_prime [2, 17, 61, 356651167] ⟨2958778081433, 3, [(2, 3), (17, 1), (61, 1), (356651167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_356651167
  · decide +kernel

theorem prime_2961496451369 : Nat.Prime 2961496451369 := by
  apply nodeValid_prime [2, 7, 13, 3313, 1227887] ⟨2961496451369, 3, [(2, 3), (7, 1), (13, 1), (3313, 1), (1227887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_3313
    · exact prime_1227887
  · decide +kernel

theorem prime_2961496463171 : Nat.Prime 2961496463171 := by
  apply nodeValid_prime [2, 5, 7, 23, 5227, 50273] ⟨2961496463171, 6, [(2, 1), (5, 1), (7, 2), (23, 1), (5227, 1), (50273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_5227
    · exact prime_50273
  · decide +kernel

theorem prime_2961496465397 : Nat.Prime 2961496465397 := by
  apply nodeValid_prime [2, 7, 149, 1217, 583279] ⟨2961496465397, 2, [(2, 2), (7, 1), (149, 1), (1217, 1), (583279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_149
    · exact prime_1217
    · exact prime_583279
  · decide +kernel

theorem prime_2964216580909 : Nat.Prime 2964216580909 := by
  apply nodeValid_prime [2, 3, 11, 41, 547711859] ⟨2964216580909, 6, [(2, 2), (3, 1), (11, 1), (41, 1), (547711859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_547711859
  · decide +kernel

theorem prime_2964216600659 : Nat.Prime 2964216600659 := by
  apply nodeValid_prime [2, 5197, 285185357] ⟨2964216600659, 2, [(2, 1), (5197, 1), (285185357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5197
    · exact prime_285185357
  · decide +kernel

theorem prime_2964216600701 : Nat.Prime 2964216600701 := by
  apply nodeValid_prime [2, 5, 29642166007] ⟨2964216600701, 2, [(2, 2), (5, 2), (29642166007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29642166007
  · decide +kernel

theorem prime_2966938387849 : Nat.Prime 2966938387849 := by
  apply nodeValid_prime [2, 3, 19, 2168814611] ⟨2966938387849, 13, [(2, 3), (3, 2), (19, 1), (2168814611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2168814611
  · decide +kernel

theorem prime_2966938388039 : Nat.Prime 2966938388039 := by
  apply nodeValid_prime [2, 19, 78077326001] ⟨2966938388039, 13, [(2, 1), (19, 1), (78077326001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_78077326001
  · decide +kernel

theorem prime_2966938406099 : Nat.Prime 2966938406099 := by
  apply nodeValid_prime [2, 17, 30293, 2880629] ⟨2966938406099, 2, [(2, 1), (17, 1), (30293, 1), (2880629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_30293
    · exact prime_2880629
  · decide +kernel

theorem prime_2969661837869 : Nat.Prime 2969661837869 := by
  apply nodeValid_prime [2, 11, 67492314497] ⟨2969661837869, 2, [(2, 2), (11, 1), (67492314497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_67492314497
  · decide +kernel

theorem prime_2969661838357 : Nat.Prime 2969661838357 := by
  apply nodeValid_prime [2, 3, 1399, 58963979] ⟨2969661838357, 5, [(2, 2), (3, 2), (1399, 1), (58963979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1399
    · exact prime_58963979
  · decide +kernel

theorem prime_2969661928081 : Nat.Prime 2969661928081 := by
  apply nodeValid_prime [2, 3, 5, 761, 827, 19661] ⟨2969661928081, 11, [(2, 4), (3, 1), (5, 1), (761, 1), (827, 1), (19661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_761
    · exact prime_827
    · exact prime_19661
  · decide +kernel

theorem prime_2972387099729 : Nat.Prime 2972387099729 := by
  apply nodeValid_prime [2, 17, 49523, 220663] ⟨2972387099729, 3, [(2, 4), (17, 1), (49523, 1), (220663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_49523
    · exact prime_220663
  · decide +kernel

theorem prime_2972387100083 : Nat.Prime 2972387100083 := by
  apply nodeValid_prime [2, 151, 2693, 3654787] ⟨2972387100083, 2, [(2, 1), (151, 1), (2693, 1), (3654787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_2693
    · exact prime_3654787
  · decide +kernel

theorem prime_2972387143393 : Nat.Prime 2972387143393 := by
  apply nodeValid_prime [2, 3, 30962366077] ⟨2972387143393, 5, [(2, 5), (3, 1), (30962366077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30962366077
  · decide +kernel

theorem prime_2975114041909 : Nat.Prime 2975114041909 := by
  apply nodeValid_prime [2, 3, 47, 5275024897] ⟨2975114041909, 2, [(2, 2), (3, 1), (47, 1), (5275024897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_5275024897
  · decide +kernel

theorem prime_2975114044429 : Nat.Prime 2975114044429 := by
  apply nodeValid_prime [2, 3, 31, 7997618399] ⟨2975114044429, 2, [(2, 2), (3, 1), (31, 1), (7997618399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_7997618399
  · decide +kernel

theorem prime_2975114046241 : Nat.Prime 2975114046241 := by
  apply nodeValid_prime [2, 3, 5, 7, 10931489] ⟨2975114046241, 19, [(2, 5), (3, 5), (5, 1), (7, 1), (10931489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_10931489
  · decide +kernel

theorem prime_2977842613561 : Nat.Prime 2977842613561 := by
  apply nodeValid_prime [2, 3, 5, 47, 527986279] ⟨2977842613561, 17, [(2, 3), (3, 1), (5, 1), (47, 1), (527986279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_527986279
  · decide +kernel

theorem prime_2977842615707 : Nat.Prime 2977842615707 := by
  apply nodeValid_prime [2, 7, 212703043979] ⟨2977842615707, 2, [(2, 1), (7, 1), (212703043979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_212703043979
  · decide +kernel

theorem prime_2977842629261 : Nat.Prime 2977842629261 := by
  apply nodeValid_prime [2, 5, 919, 162015377] ⟨2977842629261, 2, [(2, 2), (5, 1), (919, 1), (162015377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_919
    · exact prime_162015377
  · decide +kernel

theorem prime_2980572910391 : Nat.Prime 2980572910391 := by
  apply nodeValid_prime [2, 5, 61, 4886185099] ⟨2980572910391, 13, [(2, 1), (5, 1), (61, 1), (4886185099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_4886185099
  · decide +kernel

theorem prime_2980572958157 : Nat.Prime 2980572958157 := by
  apply nodeValid_prime [2, 17, 43831955267] ⟨2980572958157, 2, [(2, 2), (17, 1), (43831955267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_43831955267
  · decide +kernel

theorem prime_2980572958553 : Nat.Prime 2980572958553 := by
  apply nodeValid_prime [2, 7, 31, 101, 16999207] ⟨2980572958553, 3, [(2, 3), (7, 1), (31, 1), (101, 1), (16999207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_101
    · exact prime_16999207
  · decide +kernel

theorem prime_2983304900579 : Nat.Prime 2983304900579 := by
  apply nodeValid_prime [2, 911, 1637379199] ⟨2983304900579, 2, [(2, 1), (911, 1), (1637379199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_911
    · exact prime_1637379199
  · decide +kernel

theorem prime_2983304904829 : Nat.Prime 2983304904829 := by
  apply nodeValid_prime [2, 3, 4937, 50356237] ⟨2983304904829, 6, [(2, 2), (3, 1), (4937, 1), (50356237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4937
    · exact prime_50356237
  · decide +kernel

theorem prime_2983304906489 : Nat.Prime 2983304906489 := by
  apply nodeValid_prime [2, 113, 3300116047] ⟨2983304906489, 3, [(2, 3), (113, 1), (3300116047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_3300116047
  · decide +kernel

theorem prime_2986038593999 : Nat.Prime 2986038593999 := by
  apply nodeValid_prime [2, 257, 5809413607] ⟨2986038593999, 13, [(2, 1), (257, 1), (5809413607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_257
    · exact prime_5809413607
  · decide +kernel

theorem prime_2986038606623 : Nat.Prime 2986038606623 := by
  apply nodeValid_prime [2, 1493019303311] ⟨2986038606623, 5, [(2, 1), (1493019303311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1493019303311
  · decide +kernel

theorem prime_2986038606701 : Nat.Prime 2986038606701 := by
  apply nodeValid_prime [2, 5, 29860386067] ⟨2986038606701, 2, [(2, 2), (5, 2), (29860386067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29860386067
  · decide +kernel

theorem prime_2988773760827 : Nat.Prime 2988773760827 := by
  apply nodeValid_prime [2, 7, 23911, 1275467] ⟨2988773760827, 2, [(2, 1), (7, 2), (23911, 1), (1275467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23911
    · exact prime_1275467
  · decide +kernel

theorem prime_2988773761583 : Nat.Prime 2988773761583 := by
  apply nodeValid_prime [2, 7, 127, 1277, 1316347] ⟨2988773761583, 5, [(2, 1), (7, 1), (127, 1), (1277, 1), (1316347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_127
    · exact prime_1277
    · exact prime_1316347
  · decide +kernel

theorem prime_2988773973583 : Nat.Prime 2988773973583 := by
  apply nodeValid_prime [2, 3, 211, 2360800927] ⟨2988773973583, 3, [(2, 1), (3, 1), (211, 1), (2360800927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_2360800927
  · decide +kernel

theorem prime_2991510951001 : Nat.Prime 2991510951001 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 191, 3319] ⟨2991510951001, 7, [(2, 3), (3, 1), (5, 3), (11, 2), (13, 1), (191, 1), (3319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_191
    · exact prime_3319
  · decide +kernel

theorem prime_2991510951263 : Nat.Prime 2991510951263 := by
  apply nodeValid_prime [2, 53, 2341, 12055447] ⟨2991510951263, 5, [(2, 1), (53, 1), (2341, 1), (12055447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_2341
    · exact prime_12055447
  · decide +kernel

theorem prime_2991511049273 : Nat.Prime 2991511049273 := by
  apply nodeValid_prime [2, 167, 14447, 154991] ⟨2991511049273, 3, [(2, 3), (167, 1), (14447, 1), (154991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_14447
    · exact prime_154991
  · decide +kernel

end Sude.Lucas.Generated
