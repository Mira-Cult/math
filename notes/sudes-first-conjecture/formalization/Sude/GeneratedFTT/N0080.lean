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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0064
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0068

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_8741 : Nat.Prime 8741 := by
  apply nodeValid_prime [2, 5, 19, 23] ⟨8741, 2, [(2, 2), (5, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_10337 : Nat.Prime 10337 := by
  apply nodeValid_prime [2, 17, 19] ⟨10337, 3, [(2, 5), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_13457 : Nat.Prime 13457 := by
  apply nodeValid_prime [2, 29] ⟨13457, 3, [(2, 4), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29
  · decide +kernel

theorem prime_14827 : Nat.Prime 14827 := by
  apply nodeValid_prime [2, 3, 7, 353] ⟨14827, 2, [(2, 1), (3, 1), (7, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_353
  · decide +kernel

theorem prime_15667 : Nat.Prime 15667 := by
  apply nodeValid_prime [2, 3, 7, 373] ⟨15667, 2, [(2, 1), (3, 1), (7, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_373
  · decide +kernel

theorem prime_18379 : Nat.Prime 18379 := by
  apply nodeValid_prime [2, 3, 1021] ⟨18379, 3, [(2, 1), (3, 2), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
  · decide +kernel

theorem prime_18749 : Nat.Prime 18749 := by
  apply nodeValid_prime [2, 43, 109] ⟨18749, 2, [(2, 2), (43, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_109
  · decide +kernel

theorem prime_21221 : Nat.Prime 21221 := by
  apply nodeValid_prime [2, 5, 1061] ⟨21221, 2, [(2, 2), (5, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1061
  · decide +kernel

theorem prime_23159 : Nat.Prime 23159 := by
  apply nodeValid_prime [2, 11579] ⟨23159, 11, [(2, 1), (11579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11579
  · decide +kernel

theorem prime_26737 : Nat.Prime 26737 := by
  apply nodeValid_prime [2, 3, 557] ⟨26737, 10, [(2, 4), (3, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
  · decide +kernel

theorem prime_27763 : Nat.Prime 27763 := by
  apply nodeValid_prime [2, 3, 7, 661] ⟨27763, 3, [(2, 1), (3, 1), (7, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_661
  · decide +kernel

theorem prime_35731 : Nat.Prime 35731 := by
  apply nodeValid_prime [2, 3, 5, 397] ⟨35731, 2, [(2, 1), (3, 2), (5, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_397
  · decide +kernel

theorem prime_36913 : Nat.Prime 36913 := by
  apply nodeValid_prime [2, 3, 769] ⟨36913, 5, [(2, 4), (3, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_769
  · decide +kernel

theorem prime_39443 : Nat.Prime 39443 := by
  apply nodeValid_prime [2, 13, 37, 41] ⟨39443, 2, [(2, 1), (13, 1), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_42443 : Nat.Prime 42443 := by
  apply nodeValid_prime [2, 21221] ⟨42443, 2, [(2, 1), (21221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21221
  · decide +kernel

theorem prime_43543 : Nat.Prime 43543 := by
  apply nodeValid_prime [2, 3, 41, 59] ⟨43543, 3, [(2, 1), (3, 2), (41, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_59
  · decide +kernel

theorem prime_51971 : Nat.Prime 51971 := by
  apply nodeValid_prime [2, 5, 5197] ⟨51971, 2, [(2, 1), (5, 1), (5197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5197
  · decide +kernel

theorem prime_53719 : Nat.Prime 53719 := by
  apply nodeValid_prime [2, 3, 7, 1279] ⟨53719, 6, [(2, 1), (3, 1), (7, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1279
  · decide +kernel

theorem prime_55411 : Nat.Prime 55411 := by
  apply nodeValid_prime [2, 3, 5, 1847] ⟨55411, 2, [(2, 1), (3, 1), (5, 1), (1847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1847
  · decide +kernel

theorem prime_57397 : Nat.Prime 57397 := by
  apply nodeValid_prime [2, 3, 4783] ⟨57397, 2, [(2, 2), (3, 1), (4783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4783
  · decide +kernel

theorem prime_58031 : Nat.Prime 58031 := by
  apply nodeValid_prime [2, 5, 7, 829] ⟨58031, 7, [(2, 1), (5, 1), (7, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_829
  · decide +kernel

theorem prime_59771 : Nat.Prime 59771 := by
  apply nodeValid_prime [2, 5, 43, 139] ⟨59771, 2, [(2, 1), (5, 1), (43, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_139
  · decide +kernel

theorem prime_59951 : Nat.Prime 59951 := by
  apply nodeValid_prime [2, 5, 11, 109] ⟨59951, 11, [(2, 1), (5, 2), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_60083 : Nat.Prime 60083 := by
  apply nodeValid_prime [2, 11, 2731] ⟨60083, 2, [(2, 1), (11, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2731
  · decide +kernel

theorem prime_67763 : Nat.Prime 67763 := by
  apply nodeValid_prime [2, 17, 1993] ⟨67763, 2, [(2, 1), (17, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1993
  · decide +kernel

theorem prime_67933 : Nat.Prime 67933 := by
  apply nodeValid_prime [2, 3, 17, 37] ⟨67933, 2, [(2, 2), (3, 3), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_68141 : Nat.Prime 68141 := by
  apply nodeValid_prime [2, 5, 3407] ⟨68141, 3, [(2, 2), (5, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3407
  · decide +kernel

theorem prime_74551 : Nat.Prime 74551 := by
  apply nodeValid_prime [2, 3, 5, 7, 71] ⟨74551, 11, [(2, 1), (3, 1), (5, 2), (7, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_75181 : Nat.Prime 75181 := by
  apply nodeValid_prime [2, 3, 5, 7, 179] ⟨75181, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_179
  · decide +kernel

theorem prime_76207 : Nat.Prime 76207 := by
  apply nodeValid_prime [2, 3, 13, 977] ⟨76207, 3, [(2, 1), (3, 1), (13, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_977
  · decide +kernel

theorem prime_76507 : Nat.Prime 76507 := by
  apply nodeValid_prime [2, 3, 41, 311] ⟨76507, 2, [(2, 1), (3, 1), (41, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_311
  · decide +kernel

theorem prime_78887 : Nat.Prime 78887 := by
  apply nodeValid_prime [2, 39443] ⟨78887, 5, [(2, 1), (39443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39443
  · decide +kernel

theorem prime_82387 : Nat.Prime 82387 := by
  apply nodeValid_prime [2, 3, 23, 199] ⟨82387, 2, [(2, 1), (3, 2), (23, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_199
  · decide +kernel

theorem prime_87671 : Nat.Prime 87671 := by
  apply nodeValid_prime [2, 5, 11, 797] ⟨87671, 11, [(2, 1), (5, 1), (11, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_797
  · decide +kernel

theorem prime_96053 : Nat.Prime 96053 := by
  apply nodeValid_prime [2, 11, 37, 59] ⟨96053, 2, [(2, 2), (11, 1), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_97259 : Nat.Prime 97259 := by
  apply nodeValid_prime [2, 7, 6947] ⟨97259, 6, [(2, 1), (7, 1), (6947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6947
  · decide +kernel

theorem prime_98731 : Nat.Prime 98731 := by
  apply nodeValid_prime [2, 3, 5, 1097] ⟨98731, 2, [(2, 1), (3, 2), (5, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1097
  · decide +kernel

theorem prime_98737 : Nat.Prime 98737 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨98737, 5, [(2, 4), (3, 1), (11, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_98849 : Nat.Prime 98849 := by
  apply nodeValid_prime [2, 3089] ⟨98849, 3, [(2, 5), (3089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3089
  · decide +kernel

theorem prime_105277 : Nat.Prime 105277 := by
  apply nodeValid_prime [2, 3, 31, 283] ⟨105277, 6, [(2, 2), (3, 1), (31, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_283
  · decide +kernel

theorem prime_111871 : Nat.Prime 111871 := by
  apply nodeValid_prime [2, 3, 5, 11, 113] ⟨111871, 7, [(2, 1), (3, 2), (5, 1), (11, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_113
  · decide +kernel

theorem prime_121007 : Nat.Prime 121007 := by
  apply nodeValid_prime [2, 17, 3559] ⟨121007, 5, [(2, 1), (17, 1), (3559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3559
  · decide +kernel

theorem prime_178877 : Nat.Prime 178877 := by
  apply nodeValid_prime [2, 197, 227] ⟨178877, 2, [(2, 2), (197, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_227
  · decide +kernel

theorem prime_186283 : Nat.Prime 186283 := by
  apply nodeValid_prime [2, 3, 79, 131] ⟨186283, 3, [(2, 1), (3, 2), (79, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_131
  · decide +kernel

theorem prime_186707 : Nat.Prime 186707 := by
  apply nodeValid_prime [2, 13, 43, 167] ⟨186707, 2, [(2, 1), (13, 1), (43, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_167
  · decide +kernel

theorem prime_189463 : Nat.Prime 189463 := by
  apply nodeValid_prime [2, 3, 7, 13, 347] ⟨189463, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_347
  · decide +kernel

theorem prime_225523 : Nat.Prime 225523 := by
  apply nodeValid_prime [2, 3, 11, 17, 67] ⟨225523, 3, [(2, 1), (3, 2), (11, 1), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_237233 : Nat.Prime 237233 := by
  apply nodeValid_prime [2, 14827] ⟨237233, 3, [(2, 4), (14827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14827
  · decide +kernel

theorem prime_244561 : Nat.Prime 244561 := by
  apply nodeValid_prime [2, 3, 5, 1019] ⟨244561, 26, [(2, 4), (3, 1), (5, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1019
  · decide +kernel

theorem prime_244619 : Nat.Prime 244619 := by
  apply nodeValid_prime [2, 11, 11119] ⟨244619, 2, [(2, 1), (11, 1), (11119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11119
  · decide +kernel

theorem prime_254141 : Nat.Prime 254141 := by
  apply nodeValid_prime [2, 5, 97, 131] ⟨254141, 2, [(2, 2), (5, 1), (97, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_131
  · decide +kernel

theorem prime_285121 : Nat.Prime 285121 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨285121, 34, [(2, 6), (3, 4), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_306029 : Nat.Prime 306029 := by
  apply nodeValid_prime [2, 76507] ⟨306029, 2, [(2, 2), (76507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76507
  · decide +kernel

theorem prime_322969 : Nat.Prime 322969 := by
  apply nodeValid_prime [2, 3, 13457] ⟨322969, 7, [(2, 3), (3, 1), (13457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13457
  · decide +kernel

theorem prime_353081 : Nat.Prime 353081 := by
  apply nodeValid_prime [2, 5, 7, 13, 97] ⟨353081, 3, [(2, 3), (5, 1), (7, 1), (13, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_97
  · decide +kernel

theorem prime_364853 : Nat.Prime 364853 := by
  apply nodeValid_prime [2, 53, 1721] ⟨364853, 2, [(2, 2), (53, 1), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1721
  · decide +kernel

theorem prime_478169 : Nat.Prime 478169 := by
  apply nodeValid_prime [2, 59771] ⟨478169, 3, [(2, 3), (59771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59771
  · decide +kernel

theorem prime_495377 : Nat.Prime 495377 := by
  apply nodeValid_prime [2, 7, 4423] ⟨495377, 3, [(2, 4), (7, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4423
  · decide +kernel

theorem prime_663191 : Nat.Prime 663191 := by
  apply nodeValid_prime [2, 5, 11, 6029] ⟨663191, 11, [(2, 1), (5, 1), (11, 1), (6029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_6029
  · decide +kernel

theorem prime_677657 : Nat.Prime 677657 := by
  apply nodeValid_prime [2, 7, 12101] ⟨677657, 3, [(2, 3), (7, 1), (12101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12101
  · decide +kernel

theorem prime_720997 : Nat.Prime 720997 := by
  apply nodeValid_prime [2, 3, 60083] ⟨720997, 2, [(2, 2), (3, 1), (60083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_60083
  · decide +kernel

theorem prime_853241 : Nat.Prime 853241 := by
  apply nodeValid_prime [2, 5, 83, 257] ⟨853241, 3, [(2, 3), (5, 1), (83, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_257
  · decide +kernel

theorem prime_1318193 : Nat.Prime 1318193 := by
  apply nodeValid_prime [2, 82387] ⟨1318193, 3, [(2, 4), (82387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82387
  · decide +kernel

theorem prime_1326383 : Nat.Prime 1326383 := by
  apply nodeValid_prime [2, 663191] ⟨1326383, 5, [(2, 1), (663191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_663191
  · decide +kernel

theorem prime_1776683 : Nat.Prime 1776683 := by
  apply nodeValid_prime [2, 191, 4651] ⟨1776683, 2, [(2, 1), (191, 1), (4651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_4651
  · decide +kernel

theorem prime_1877951 : Nat.Prime 1877951 := by
  apply nodeValid_prime [2, 5, 23, 71] ⟨1877951, 11, [(2, 1), (5, 2), (23, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_71
  · decide +kernel

theorem prime_2883989 : Nat.Prime 2883989 := by
  apply nodeValid_prime [2, 720997] ⟨2883989, 2, [(2, 2), (720997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_720997
  · decide +kernel

theorem prime_3009373 : Nat.Prime 3009373 := by
  apply nodeValid_prime [2, 3, 19, 67, 197] ⟨3009373, 15, [(2, 2), (3, 1), (19, 1), (67, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_67
    · exact prime_197
  · decide +kernel

theorem prime_3228437 : Nat.Prime 3228437 := by
  apply nodeValid_prime [2, 17, 197, 241] ⟨3228437, 2, [(2, 2), (17, 1), (197, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_197
    · exact prime_241
  · decide +kernel

theorem prime_3963017 : Nat.Prime 3963017 := by
  apply nodeValid_prime [2, 495377] ⟨3963017, 3, [(2, 3), (495377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_495377
  · decide +kernel

theorem prime_4470793 : Nat.Prime 4470793 := by
  apply nodeValid_prime [2, 3, 186283] ⟨4470793, 5, [(2, 3), (3, 1), (186283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_186283
  · decide +kernel

theorem prime_5660591 : Nat.Prime 5660591 := by
  apply nodeValid_prime [2, 5, 13, 43543] ⟨5660591, 19, [(2, 1), (5, 1), (13, 1), (43543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43543
  · decide +kernel

theorem prime_6340463 : Nat.Prime 6340463 := by
  apply nodeValid_prime [2, 61, 51971] ⟨6340463, 5, [(2, 1), (61, 1), (51971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_51971
  · decide +kernel

theorem prime_8118829 : Nat.Prime 8118829 := by
  apply nodeValid_prime [2, 3, 225523] ⟨8118829, 2, [(2, 2), (3, 2), (225523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_225523
  · decide +kernel

theorem prime_9873701 : Nat.Prime 9873701 := by
  apply nodeValid_prime [2, 5, 98737] ⟨9873701, 2, [(2, 2), (5, 2), (98737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_98737
  · decide +kernel

theorem prime_12674227 : Nat.Prime 12674227 := by
  apply nodeValid_prime [2, 3, 31, 68141] ⟨12674227, 3, [(2, 1), (3, 1), (31, 1), (68141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_68141
  · decide +kernel

theorem prime_12879851 : Nat.Prime 12879851 := by
  apply nodeValid_prime [2, 5, 173, 1489] ⟨12879851, 2, [(2, 1), (5, 2), (173, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_1489
  · decide +kernel

theorem prime_14492287 : Nat.Prime 14492287 := by
  apply nodeValid_prime [2, 3, 29, 27763] ⟨14492287, 3, [(2, 1), (3, 2), (29, 1), (27763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_27763
  · decide +kernel

theorem prime_15975307 : Nat.Prime 15975307 := by
  apply nodeValid_prime [2, 3, 10957] ⟨15975307, 14, [(2, 1), (3, 6), (10957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10957
  · decide +kernel

theorem prime_17386153 : Nat.Prime 17386153 := by
  apply nodeValid_prime [2, 3, 7, 37, 2797] ⟨17386153, 10, [(2, 3), (3, 1), (7, 1), (37, 1), (2797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_2797
  · decide +kernel

theorem prime_33985403 : Nat.Prime 33985403 := by
  apply nodeValid_prime [2, 11, 53, 29147] ⟨33985403, 5, [(2, 1), (11, 1), (53, 1), (29147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_29147
  · decide +kernel

theorem prime_34277743 : Nat.Prime 34277743 := by
  apply nodeValid_prime [2, 3, 457, 463] ⟨34277743, 3, [(2, 1), (3, 4), (457, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_457
    · exact prime_463
  · decide +kernel

theorem prime_35100917 : Nat.Prime 35100917 := by
  apply nodeValid_prime [2, 47, 186707] ⟨35100917, 2, [(2, 2), (47, 1), (186707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_186707
  · decide +kernel

theorem prime_36775903 : Nat.Prime 36775903 := by
  apply nodeValid_prime [2, 3, 47, 130411] ⟨36775903, 13, [(2, 1), (3, 1), (47, 1), (130411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_130411
  · decide +kernel

theorem prime_44478877 : Nat.Prime 44478877 := by
  apply nodeValid_prime [2, 3, 13, 285121] ⟨44478877, 5, [(2, 2), (3, 1), (13, 1), (285121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_285121
  · decide +kernel

theorem prime_47439671 : Nat.Prime 47439671 := by
  apply nodeValid_prime [2, 5, 89, 151, 353] ⟨47439671, 11, [(2, 1), (5, 1), (89, 1), (151, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_151
    · exact prime_353
  · decide +kernel

theorem prime_59391377 : Nat.Prime 59391377 := by
  apply nodeValid_prime [2, 11, 53, 6367] ⟨59391377, 5, [(2, 4), (11, 1), (53, 1), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_6367
  · decide +kernel

theorem prime_69215737 : Nat.Prime 69215737 := by
  apply nodeValid_prime [2, 3, 2883989] ⟨69215737, 5, [(2, 3), (3, 1), (2883989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2883989
  · decide +kernel

theorem prime_123757313 : Nat.Prime 123757313 := by
  apply nodeValid_prime [2, 7, 69061] ⟨123757313, 3, [(2, 8), (7, 1), (69061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_69061
  · decide +kernel

theorem prime_134717327 : Nat.Prime 134717327 := by
  apply nodeValid_prime [2, 1123, 59981] ⟨134717327, 5, [(2, 1), (1123, 1), (59981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1123
    · exact prime_59981
  · decide +kernel

theorem prime_146465833 : Nat.Prime 146465833 := by
  apply nodeValid_prime [2, 3, 19, 37, 8681] ⟨146465833, 7, [(2, 3), (3, 1), (19, 1), (37, 1), (8681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_8681
  · decide +kernel

theorem prime_266299447 : Nat.Prime 266299447 := by
  apply nodeValid_prime [2, 3, 7, 6340463] ⟨266299447, 5, [(2, 1), (3, 1), (7, 1), (6340463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6340463
  · decide +kernel

theorem prime_305477483 : Nat.Prime 305477483 := by
  apply nodeValid_prime [2, 601, 254141] ⟨305477483, 2, [(2, 1), (601, 1), (254141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_254141
  · decide +kernel

theorem prime_569276053 : Nat.Prime 569276053 := by
  apply nodeValid_prime [2, 3, 47439671] ⟨569276053, 6, [(2, 2), (3, 1), (47439671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47439671
  · decide +kernel

theorem prime_662194249 : Nat.Prime 662194249 := by
  apply nodeValid_prime [2, 3, 367, 75181] ⟨662194249, 11, [(2, 3), (3, 1), (367, 1), (75181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_75181
  · decide +kernel

theorem prime_852807841 : Nat.Prime 852807841 := by
  apply nodeValid_prime [2, 3, 5, 1776683] ⟨852807841, 11, [(2, 5), (3, 1), (5, 1), (1776683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1776683
  · decide +kernel

theorem prime_882621673 : Nat.Prime 882621673 := by
  apply nodeValid_prime [2, 3, 36775903] ⟨882621673, 5, [(2, 3), (3, 1), (36775903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36775903
  · decide +kernel

theorem prime_1249933693 : Nat.Prime 1249933693 := by
  apply nodeValid_prime [2, 3, 7, 277, 53719] ⟨1249933693, 2, [(2, 2), (3, 1), (7, 1), (277, 1), (53719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_277
    · exact prime_53719
  · decide +kernel

theorem prime_5616857231 : Nat.Prime 5616857231 := by
  apply nodeValid_prime [2, 5, 59, 67, 151, 941] ⟨5616857231, 13, [(2, 1), (5, 1), (59, 1), (67, 1), (151, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_67
    · exact prime_151
    · exact prime_941
  · decide +kernel

theorem prime_6371922647 : Nat.Prime 6371922647 := by
  apply nodeValid_prime [2, 251, 677, 18749] ⟨6371922647, 5, [(2, 1), (251, 1), (677, 1), (18749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_677
    · exact prime_18749
  · decide +kernel

theorem prime_7796850407 : Nat.Prime 7796850407 := by
  apply nodeValid_prime [2, 269, 14492287] ⟨7796850407, 5, [(2, 1), (269, 1), (14492287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_14492287
  · decide +kernel

theorem prime_8242894769 : Nat.Prime 8242894769 := by
  apply nodeValid_prime [2, 5297, 97259] ⟨8242894769, 3, [(2, 4), (5297, 1), (97259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5297
    · exact prime_97259
  · decide +kernel

theorem prime_8269966297 : Nat.Prime 8269966297 := by
  apply nodeValid_prime [2, 3, 19, 23, 87613] ⟨8269966297, 10, [(2, 3), (3, 3), (19, 1), (23, 1), (87613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_87613
  · decide +kernel

theorem prime_8786092591 : Nat.Prime 8786092591 := by
  apply nodeValid_prime [2, 3, 5, 11, 29, 306029] ⟨8786092591, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (29, 1), (306029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_306029
  · decide +kernel

theorem prime_9673854917 : Nat.Prime 9673854917 := by
  apply nodeValid_prime [2, 11, 29, 31, 244561] ⟨9673854917, 2, [(2, 2), (11, 1), (29, 1), (31, 1), (244561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_31
    · exact prime_244561
  · decide +kernel

theorem prime_11441367913 : Nat.Prime 11441367913 := by
  apply nodeValid_prime [2, 3, 13, 29, 457, 2767] ⟨11441367913, 7, [(2, 3), (3, 1), (13, 1), (29, 1), (457, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_457
    · exact prime_2767
  · decide +kernel

theorem prime_13508476019 : Nat.Prime 13508476019 := by
  apply nodeValid_prime [2, 19, 53, 163, 41149] ⟨13508476019, 2, [(2, 1), (19, 1), (53, 1), (163, 1), (41149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_53
    · exact prime_163
    · exact prime_41149
  · decide +kernel

theorem prime_15350541139 : Nat.Prime 15350541139 := by
  apply nodeValid_prime [2, 3, 852807841] ⟨15350541139, 2, [(2, 1), (3, 2), (852807841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_852807841
  · decide +kernel

theorem prime_20932246121 : Nat.Prime 20932246121 := by
  apply nodeValid_prime [2, 5, 53, 9873701] ⟨20932246121, 6, [(2, 3), (5, 1), (53, 1), (9873701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_9873701
  · decide +kernel

theorem prime_29183950307 : Nat.Prime 29183950307 := by
  apply nodeValid_prime [2, 7, 29, 41, 89, 19699] ⟨29183950307, 5, [(2, 1), (7, 1), (29, 1), (41, 1), (89, 1), (19699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_41
    · exact prime_89
    · exact prime_19699
  · decide +kernel

theorem prime_33178925557 : Nat.Prime 33178925557 := by
  apply nodeValid_prime [2, 3, 7, 1669, 78887] ⟨33178925557, 2, [(2, 2), (3, 2), (7, 1), (1669, 1), (78887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1669
    · exact prime_78887
  · decide +kernel

theorem prime_33352385263 : Nat.Prime 33352385263 := by
  apply nodeValid_prime [2, 3, 7, 19, 397, 105277] ⟨33352385263, 6, [(2, 1), (3, 1), (7, 1), (19, 1), (397, 1), (105277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_397
    · exact prime_105277
  · decide +kernel

theorem prime_43775668483 : Nat.Prime 43775668483 := by
  apply nodeValid_prime [2, 3, 7, 13, 23, 181, 19259] ⟨43775668483, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (23, 1), (181, 1), (19259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_181
    · exact prime_19259
  · decide +kernel

theorem prime_52826458031 : Nat.Prime 52826458031 := by
  apply nodeValid_prime [2, 5, 73, 5527, 13093] ⟨52826458031, 7, [(2, 1), (5, 1), (73, 1), (5527, 1), (13093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_5527
    · exact prime_13093
  · decide +kernel

theorem prime_168330789409 : Nat.Prime 168330789409 := by
  apply nodeValid_prime [2, 3, 19, 193, 478169] ⟨168330789409, 11, [(2, 5), (3, 1), (19, 1), (193, 1), (478169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_193
    · exact prime_478169
  · decide +kernel

theorem prime_198658274701 : Nat.Prime 198658274701 := by
  apply nodeValid_prime [2, 3, 5, 662194249] ⟨198658274701, 10, [(2, 2), (3, 1), (5, 2), (662194249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_662194249
  · decide +kernel

theorem prime_251710094087 : Nat.Prime 251710094087 := by
  apply nodeValid_prime [2, 11, 11441367913] ⟨251710094087, 5, [(2, 1), (11, 1), (11441367913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_11441367913
  · decide +kernel

theorem prime_1976226413377 : Nat.Prime 1976226413377 := by
  apply nodeValid_prime [2, 3, 431, 2543, 9391] ⟨1976226413377, 5, [(2, 6), (3, 1), (431, 1), (2543, 1), (9391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
    · exact prime_2543
    · exact prime_9391
  · decide +kernel

theorem prime_1976226413387 : Nat.Prime 1976226413387 := by
  apply nodeValid_prime [2, 19, 109, 113, 587, 7193] ⟨1976226413387, 2, [(2, 1), (19, 1), (109, 1), (113, 1), (587, 1), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_109
    · exact prime_113
    · exact prime_587
    · exact prime_7193
  · decide +kernel

theorem prime_1976226444037 : Nat.Prime 1976226444037 := by
  apply nodeValid_prime [2, 3, 13, 55411, 76207] ⟨1976226444037, 2, [(2, 2), (3, 2), (13, 1), (55411, 1), (76207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_55411
    · exact prime_76207
  · decide +kernel

theorem prime_1978294743977 : Nat.Prime 1978294743977 := by
  apply nodeValid_prime [2, 109, 179, 12674227] ⟨1978294743977, 3, [(2, 3), (109, 1), (179, 1), (12674227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_179
    · exact prime_12674227
  · decide +kernel

theorem prime_1978294744561 : Nat.Prime 1978294744561 := by
  apply nodeValid_prime [2, 3, 5, 8242894769] ⟨1978294744561, 17, [(2, 4), (3, 1), (5, 1), (8242894769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8242894769
  · decide +kernel

theorem prime_1978294782293 : Nat.Prime 1978294782293 := by
  apply nodeValid_prime [2, 563, 3719, 236209] ⟨1978294782293, 2, [(2, 2), (563, 1), (3719, 1), (236209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_3719
    · exact prime_236209
  · decide +kernel

theorem prime_1980364522627 : Nat.Prime 1980364522627 := by
  apply nodeValid_prime [2, 3, 7, 127, 123757313] ⟨1980364522627, 2, [(2, 1), (3, 2), (7, 1), (127, 1), (123757313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_127
    · exact prime_123757313
  · decide +kernel

theorem prime_1980364584109 : Nat.Prime 1980364584109 := by
  apply nodeValid_prime [2, 3, 36913, 4470793] ⟨1980364584109, 2, [(2, 2), (3, 1), (36913, 1), (4470793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36913
    · exact prime_4470793
  · decide +kernel

theorem prime_1982435845979 : Nat.Prime 1982435845979 := by
  apply nodeValid_prime [2, 7, 35731, 3963017] ⟨1982435845979, 2, [(2, 1), (7, 1), (35731, 1), (3963017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_35731
    · exact prime_3963017
  · decide +kernel

theorem prime_1982435871329 : Nat.Prime 1982435871329 := by
  apply nodeValid_prime [2, 11, 17, 29, 47, 89, 2731] ⟨1982435871329, 3, [(2, 5), (11, 1), (17, 1), (29, 1), (47, 1), (89, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_29
    · exact prime_47
    · exact prime_89
    · exact prime_2731
  · decide +kernel

theorem prime_1982435871707 : Nat.Prime 1982435871707 := by
  apply nodeValid_prime [2, 163, 61519, 98849] ⟨1982435871707, 2, [(2, 1), (163, 1), (61519, 1), (98849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_61519
    · exact prime_98849
  · decide +kernel

theorem prime_1984508573261 : Nat.Prime 1984508573261 := by
  apply nodeValid_prime [2, 5, 197, 7433, 67763] ⟨1984508573261, 2, [(2, 2), (5, 1), (197, 1), (7433, 1), (67763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
    · exact prime_7433
    · exact prime_67763
  · decide +kernel

theorem prime_1984508620877 : Nat.Prime 1984508620877 := by
  apply nodeValid_prime [2, 17, 29183950307] ⟨1984508620877, 2, [(2, 2), (17, 1), (29183950307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29183950307
  · decide +kernel

theorem prime_1984508621357 : Nat.Prime 1984508621357 := by
  apply nodeValid_prime [2, 1723, 15667, 18379] ⟨1984508621357, 2, [(2, 2), (1723, 1), (15667, 1), (18379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1723
    · exact prime_15667
    · exact prime_18379
  · decide +kernel

theorem prime_1986582746963 : Nat.Prime 1986582746963 := by
  apply nodeValid_prime [2, 11, 2657, 33985403] ⟨1986582746963, 2, [(2, 1), (11, 1), (2657, 1), (33985403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2657
    · exact prime_33985403
  · decide +kernel

theorem prime_1986582747011 : Nat.Prime 1986582747011 := by
  apply nodeValid_prime [2, 5, 198658274701] ⟨1986582747011, 2, [(2, 1), (5, 1), (198658274701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_198658274701
  · decide +kernel

theorem prime_1986582760651 : Nat.Prime 1986582760651 := by
  apply nodeValid_prime [2, 3, 5, 17, 197, 1318193] ⟨1986582760651, 3, [(2, 1), (3, 2), (5, 2), (17, 1), (197, 1), (1318193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_197
    · exact prime_1318193
  · decide +kernel

theorem prime_1988658414331 : Nat.Prime 1988658414331 := by
  apply nodeValid_prime [2, 3, 5, 7, 31, 305477483] ⟨1988658414331, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (305477483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_305477483
  · decide +kernel

theorem prime_1988658450577 : Nat.Prime 1988658450577 := by
  apply nodeValid_prime [2, 3, 7, 8118829] ⟨1988658450577, 15, [(2, 4), (3, 7), (7, 1), (8118829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8118829
  · decide +kernel

theorem prime_1988658451387 : Nat.Prime 1988658451387 := by
  apply nodeValid_prime [2, 3, 227, 563, 96053] ⟨1988658451387, 5, [(2, 1), (3, 4), (227, 1), (563, 1), (96053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_563
    · exact prime_96053
  · decide +kernel

theorem prime_1990735530263 : Nat.Prime 1990735530263 := by
  apply nodeValid_prime [2, 109, 709, 12879851] ⟨1990735530263, 5, [(2, 1), (109, 1), (709, 1), (12879851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_709
    · exact prime_12879851
  · decide +kernel

theorem prime_1990735533421 : Nat.Prime 1990735533421 := by
  apply nodeValid_prime [2, 3, 5, 33178925557] ⟨1990735533421, 6, [(2, 2), (3, 1), (5, 1), (33178925557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_33178925557
  · decide +kernel

theorem prime_1990735533469 : Nat.Prime 1990735533469 := by
  apply nodeValid_prime [2, 3, 11, 17, 1451, 67933] ⟨1990735533469, 6, [(2, 2), (3, 3), (11, 1), (17, 1), (1451, 1), (67933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_1451
    · exact prime_67933
  · decide +kernel

theorem prime_1992814112903 : Nat.Prime 1992814112903 := by
  apply nodeValid_prime [2, 103, 9673854917] ⟨1992814112903, 5, [(2, 1), (103, 1), (9673854917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_9673854917
  · decide +kernel

theorem prime_1992814123799 : Nat.Prime 1992814123799 := by
  apply nodeValid_prime [2, 6803, 146465833] ⟨1992814123799, 7, [(2, 1), (6803, 1), (146465833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6803
    · exact prime_146465833
  · decide +kernel

theorem prime_1992814123877 : Nat.Prime 1992814123877 := by
  apply nodeValid_prime [2, 17, 47, 2549, 244619] ⟨1992814123877, 2, [(2, 2), (17, 1), (47, 1), (2549, 1), (244619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_2549
    · exact prime_244619
  · decide +kernel

theorem prime_1994894159039 : Nat.Prime 1994894159039 := by
  apply nodeValid_prime [2, 11, 83, 193, 5660591] ⟨1994894159039, 13, [(2, 1), (11, 1), (83, 1), (193, 1), (5660591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83
    · exact prime_193
    · exact prime_5660591
  · decide +kernel

theorem prime_1994894174029 : Nat.Prime 1994894174029 := by
  apply nodeValid_prime [2, 3, 7, 19, 1249933693] ⟨1994894174029, 6, [(2, 2), (3, 1), (7, 1), (19, 1), (1249933693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_1249933693
  · decide +kernel

theorem prime_1994894178217 : Nat.Prime 1994894178217 := by
  apply nodeValid_prime [2, 3, 617, 134717327] ⟨1994894178217, 5, [(2, 3), (3, 1), (617, 1), (134717327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_617
    · exact prime_134717327
  · decide +kernel

theorem prime_1996975660249 : Nat.Prime 1996975660249 := by
  apply nodeValid_prime [2, 3, 467, 59391377] ⟨1996975660249, 14, [(2, 3), (3, 2), (467, 1), (59391377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_59391377
  · decide +kernel

theorem prime_1996975660331 : Nat.Prime 1996975660331 := by
  apply nodeValid_prime [2, 5, 7, 17, 23, 739, 98731] ⟨1996975660331, 2, [(2, 1), (5, 1), (7, 1), (17, 1), (23, 1), (739, 1), (98731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_739
    · exact prime_98731
  · decide +kernel

theorem prime_1996975672921 : Nat.Prime 1996975672921 := by
  apply nodeValid_prime [2, 3, 5, 10337, 178877] ⟨1996975672921, 14, [(2, 3), (3, 3), (5, 1), (10337, 1), (178877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10337
    · exact prime_178877
  · decide +kernel

theorem prime_1999058647501 : Nat.Prime 1999058647501 := by
  apply nodeValid_prime [2, 3, 5, 3323, 26737] ⟨1999058647501, 2, [(2, 2), (3, 2), (5, 4), (3323, 1), (26737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3323
    · exact prime_26737
  · decide +kernel

theorem prime_1999058647889 : Nat.Prime 1999058647889 := by
  apply nodeValid_prime [2, 53, 44478877] ⟨1999058647889, 3, [(2, 4), (53, 2), (44478877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_44478877
  · decide +kernel

theorem prime_1999058661077 : Nat.Prime 1999058661077 := by
  apply nodeValid_prime [2, 503, 16573, 59951] ⟨1999058661077, 2, [(2, 2), (503, 1), (16573, 1), (59951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_503
    · exact prime_16573
    · exact prime_59951
  · decide +kernel

theorem prime_2001143054623 : Nat.Prime 2001143054623 := by
  apply nodeValid_prime [2, 3, 29, 31, 8741, 42443] ⟨2001143054623, 6, [(2, 1), (3, 1), (29, 1), (31, 1), (8741, 1), (42443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
    · exact prime_8741
    · exact prime_42443
  · decide +kernel

theorem prime_2001143055421 : Nat.Prime 2001143055421 := by
  apply nodeValid_prime [2, 3, 5, 53, 1871, 12457] ⟨2001143055421, 2, [(2, 2), (3, 4), (5, 1), (53, 1), (1871, 1), (12457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_1871
    · exact prime_12457
  · decide +kernel

theorem prime_2001143115781 : Nat.Prime 2001143115781 := by
  apply nodeValid_prime [2, 3, 5, 33352385263] ⟨2001143115781, 2, [(2, 2), (3, 1), (5, 1), (33352385263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_33352385263
  · decide +kernel

theorem prime_2003229045031 : Nat.Prime 2003229045031 := by
  apply nodeValid_prime [2, 3, 5, 397, 461, 364853] ⟨2003229045031, 6, [(2, 1), (3, 1), (5, 1), (397, 1), (461, 1), (364853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_397
    · exact prime_461
    · exact prime_364853
  · decide +kernel

theorem prime_2003229110749 : Nat.Prime 2003229110749 := by
  apply nodeValid_prime [2, 3, 19, 8786092591] ⟨2003229110749, 2, [(2, 2), (3, 1), (19, 1), (8786092591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_8786092591
  · decide +kernel

theorem prime_2003229111211 : Nat.Prime 2003229111211 := by
  apply nodeValid_prime [2, 3, 5, 31, 37, 1877951] ⟨2003229111211, 2, [(2, 1), (3, 1), (5, 1), (31, 2), (37, 1), (1877951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_37
    · exact prime_1877951
  · decide +kernel

theorem prime_2005316386483 : Nat.Prime 2005316386483 := by
  apply nodeValid_prime [2, 3, 20921, 15975307] ⟨2005316386483, 2, [(2, 1), (3, 1), (20921, 1), (15975307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20921
    · exact prime_15975307
  · decide +kernel

theorem prime_2005316387329 : Nat.Prime 2005316387329 := by
  apply nodeValid_prime [2, 3, 10789, 121007] ⟨2005316387329, 7, [(2, 9), (3, 1), (10789, 1), (121007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10789
    · exact prime_121007
  · decide +kernel

theorem prime_2005316441057 : Nat.Prime 2005316441057 := by
  apply nodeValid_prime [2, 71, 882621673] ⟨2005316441057, 3, [(2, 5), (71, 1), (882621673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_882621673
  · decide +kernel

theorem prime_2007405305077 : Nat.Prime 2007405305077 := by
  apply nodeValid_prime [2, 3, 71, 6673, 353081] ⟨2007405305077, 2, [(2, 2), (3, 1), (71, 1), (6673, 1), (353081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_6673
    · exact prime_353081
  · decide +kernel

theorem prime_2007405403907 : Nat.Prime 2007405403907 := by
  apply nodeValid_prime [2, 7, 17, 23, 4919, 74551] ⟨2007405403907, 2, [(2, 1), (7, 1), (17, 1), (23, 1), (4919, 1), (74551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_4919
    · exact prime_74551
  · decide +kernel

theorem prime_2007405405179 : Nat.Prime 2007405405179 := by
  apply nodeValid_prime [2, 19, 52826458031] ⟨2007405405179, 2, [(2, 1), (19, 1), (52826458031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_52826458031
  · decide +kernel

theorem prime_2009495627063 : Nat.Prime 2009495627063 := by
  apply nodeValid_prime [2, 7, 11, 266299447] ⟨2009495627063, 5, [(2, 1), (7, 3), (11, 1), (266299447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_266299447
  · decide +kernel

theorem prime_2009495627617 : Nat.Prime 2009495627617 := by
  apply nodeValid_prime [2, 3, 20932246121] ⟨2009495627617, 5, [(2, 5), (3, 1), (20932246121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20932246121
  · decide +kernel

theorem prime_2009495637907 : Nat.Prime 2009495637907 := by
  apply nodeValid_prime [2, 3, 173, 179, 467, 23159] ⟨2009495637907, 2, [(2, 1), (3, 1), (173, 1), (179, 1), (467, 1), (23159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_179
    · exact prime_467
    · exact prime_23159
  · decide +kernel

theorem prime_2011587404531 : Nat.Prime 2011587404531 := by
  apply nodeValid_prime [2, 5, 11, 263, 367, 189463] ⟨2011587404531, 2, [(2, 1), (5, 1), (11, 1), (263, 1), (367, 1), (189463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_263
    · exact prime_367
    · exact prime_189463
  · decide +kernel

theorem prime_2011587405007 : Nat.Prime 2011587405007 := by
  apply nodeValid_prime [2, 3, 43, 7796850407] ⟨2011587405007, 3, [(2, 1), (3, 1), (43, 1), (7796850407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_7796850407
  · decide +kernel

theorem prime_2011587439709 : Nat.Prime 2011587439709 := by
  apply nodeValid_prime [2, 7, 11, 17, 3228437] ⟨2011587439709, 2, [(2, 2), (7, 2), (11, 1), (17, 2), (3228437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_3228437
  · decide +kernel

theorem prime_2013680709977 : Nat.Prime 2013680709977 := by
  apply nodeValid_prime [2, 13, 59951, 322969] ⟨2013680709977, 3, [(2, 3), (13, 1), (59951, 1), (322969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_59951
    · exact prime_322969
  · decide +kernel

theorem prime_2013680750219 : Nat.Prime 2013680750219 := by
  apply nodeValid_prime [2, 23, 43775668483] ⟨2013680750219, 6, [(2, 1), (23, 1), (43775668483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43775668483
  · decide +kernel

theorem prime_2013680752697 : Nat.Prime 2013680752697 := by
  apply nodeValid_prime [2, 251710094087] ⟨2013680752697, 3, [(2, 3), (251710094087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_251710094087
  · decide +kernel

theorem prime_2015775454951 : Nat.Prime 2015775454951 := by
  apply nodeValid_prime [2, 3, 5, 53, 5147, 16421] ⟨2015775454951, 3, [(2, 1), (3, 2), (5, 2), (53, 1), (5147, 1), (16421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_5147
    · exact prime_16421
  · decide +kernel

theorem prime_2015775461477 : Nat.Prime 2015775461477 := by
  apply nodeValid_prime [2, 7, 293, 35100917] ⟨2015775461477, 2, [(2, 2), (7, 2), (293, 1), (35100917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_293
    · exact prime_35100917
  · decide +kernel

theorem prime_2017871689487 : Nat.Prime 2017871689487 := by
  apply nodeValid_prime [2, 58031, 17386153] ⟨2017871689487, 5, [(2, 1), (58031, 1), (17386153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_58031
    · exact prime_17386153
  · decide +kernel

theorem prime_2017871776007 : Nat.Prime 2017871776007 := by
  apply nodeValid_prime [2, 211, 227, 367, 57397] ⟨2017871776007, 5, [(2, 1), (211, 1), (227, 1), (367, 1), (57397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_227
    · exact prime_367
    · exact prime_57397
  · decide +kernel

theorem prime_2017871776469 : Nat.Prime 2017871776469 := by
  apply nodeValid_prime [2, 61, 8269966297] ⟨2017871776469, 2, [(2, 2), (61, 1), (8269966297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_8269966297
  · decide +kernel

theorem prime_2019969401299 : Nat.Prime 2019969401299 := by
  apply nodeValid_prime [2, 3, 111871, 3009373] ⟨2019969401299, 2, [(2, 1), (3, 1), (111871, 1), (3009373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_111871
    · exact prime_3009373
  · decide +kernel

theorem prime_2019969472799 : Nat.Prime 2019969472799 := by
  apply nodeValid_prime [2, 17, 87671, 677657] ⟨2019969472799, 11, [(2, 1), (17, 1), (87671, 1), (677657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_87671
    · exact prime_677657
  · decide +kernel

theorem prime_2019969472909 : Nat.Prime 2019969472909 := by
  apply nodeValid_prime [2, 3, 168330789409] ⟨2019969472909, 2, [(2, 2), (3, 1), (168330789409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_168330789409
  · decide +kernel

theorem prime_2022068540257 : Nat.Prime 2022068540257 := by
  apply nodeValid_prime [2, 3, 37, 569276053] ⟨2022068540257, 5, [(2, 5), (3, 1), (37, 1), (569276053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_569276053
  · decide +kernel

theorem prime_2022068540719 : Nat.Prime 2022068540719 := by
  apply nodeValid_prime [2, 3, 541, 69215737] ⟨2022068540719, 3, [(2, 1), (3, 3), (541, 1), (69215737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
    · exact prime_69215737
  · decide +kernel

theorem prime_2022068603161 : Nat.Prime 2022068603161 := by
  apply nodeValid_prime [2, 3, 5, 5616857231] ⟨2022068603161, 7, [(2, 3), (3, 2), (5, 1), (5616857231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5616857231
  · decide +kernel

theorem prime_2024169221407 : Nat.Prime 2024169221407 := by
  apply nodeValid_prime [2, 3, 53, 4799, 1326383] ⟨2024169221407, 13, [(2, 1), (3, 1), (53, 1), (4799, 1), (1326383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_4799
    · exact prime_1326383
  · decide +kernel

theorem prime_2024169221531 : Nat.Prime 2024169221531 := by
  apply nodeValid_prime [2, 5, 237233, 853241] ⟨2024169221531, 2, [(2, 1), (5, 1), (237233, 1), (853241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_237233
    · exact prime_853241
  · decide +kernel

theorem prime_2024169279637 : Nat.Prime 2024169279637 := by
  apply nodeValid_prime [2, 3, 7, 19, 37, 34277743] ⟨2024169279637, 2, [(2, 2), (3, 1), (7, 1), (19, 1), (37, 1), (34277743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_37
    · exact prime_34277743
  · decide +kernel

theorem prime_2026271401747 : Nat.Prime 2026271401747 := by
  apply nodeValid_prime [2, 3, 53, 6371922647] ⟨2026271401747, 2, [(2, 1), (3, 1), (53, 1), (6371922647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_6371922647
  · decide +kernel

theorem prime_2026271402851 : Nat.Prime 2026271402851 := by
  apply nodeValid_prime [2, 3, 5, 13508476019] ⟨2026271402851, 2, [(2, 1), (3, 1), (5, 2), (13508476019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13508476019
  · decide +kernel

theorem prime_2026271430349 : Nat.Prime 2026271430349 := by
  apply nodeValid_prime [2, 3, 11, 15350541139] ⟨2026271430349, 2, [(2, 2), (3, 1), (11, 1), (15350541139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_15350541139
  · decide +kernel

end Sude.Lucas.Generated
