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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0095

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9719 : Nat.Prime 9719 := by
  apply nodeValid_prime [2, 43, 113] ⟨9719, 17, [(2, 1), (43, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_113
  · decide +kernel

theorem prime_15139 : Nat.Prime 15139 := by
  apply nodeValid_prime [2, 3, 29] ⟨15139, 2, [(2, 1), (3, 2), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_17881 : Nat.Prime 17881 := by
  apply nodeValid_prime [2, 3, 5, 149] ⟨17881, 7, [(2, 3), (3, 1), (5, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
  · decide +kernel

theorem prime_20627 : Nat.Prime 20627 := by
  apply nodeValid_prime [2, 10313] ⟨20627, 2, [(2, 1), (10313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10313
  · decide +kernel

theorem prime_24623 : Nat.Prime 24623 := by
  apply nodeValid_prime [2, 13, 947] ⟨24623, 5, [(2, 1), (13, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_947
  · decide +kernel

theorem prime_24919 : Nat.Prime 24919 := by
  apply nodeValid_prime [2, 3, 4153] ⟨24919, 3, [(2, 1), (3, 1), (4153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4153
  · decide +kernel

theorem prime_25657 : Nat.Prime 25657 := by
  apply nodeValid_prime [2, 3, 1069] ⟨25657, 5, [(2, 3), (3, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1069
  · decide +kernel

theorem prime_27259 : Nat.Prime 27259 := by
  apply nodeValid_prime [2, 3, 7, 11, 59] ⟨27259, 2, [(2, 1), (3, 1), (7, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_29789 : Nat.Prime 29789 := by
  apply nodeValid_prime [2, 11, 677] ⟨29789, 2, [(2, 2), (11, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_677
  · decide +kernel

theorem prime_30313 : Nat.Prime 30313 := by
  apply nodeValid_prime [2, 3, 421] ⟨30313, 5, [(2, 3), (3, 2), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
  · decide +kernel

theorem prime_33203 : Nat.Prime 33203 := by
  apply nodeValid_prime [2, 13, 1277] ⟨33203, 2, [(2, 1), (13, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1277
  · decide +kernel

theorem prime_34549 : Nat.Prime 34549 := by
  apply nodeValid_prime [2, 3, 2879] ⟨34549, 2, [(2, 2), (3, 1), (2879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2879
  · decide +kernel

theorem prime_40933 : Nat.Prime 40933 := by
  apply nodeValid_prime [2, 3, 379] ⟨40933, 2, [(2, 2), (3, 3), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
  · decide +kernel

theorem prime_59929 : Nat.Prime 59929 := by
  apply nodeValid_prime [2, 3, 11, 227] ⟨59929, 19, [(2, 3), (3, 1), (11, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_227
  · decide +kernel

theorem prime_72229 : Nat.Prime 72229 := by
  apply nodeValid_prime [2, 3, 13, 463] ⟨72229, 2, [(2, 2), (3, 1), (13, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_463
  · decide +kernel

theorem prime_76039 : Nat.Prime 76039 := by
  apply nodeValid_prime [2, 3, 19, 23, 29] ⟨76039, 12, [(2, 1), (3, 1), (19, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_78857 : Nat.Prime 78857 := by
  apply nodeValid_prime [2, 9857] ⟨78857, 3, [(2, 3), (9857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9857
  · decide +kernel

theorem prime_79367 : Nat.Prime 79367 := by
  apply nodeValid_prime [2, 7, 5669] ⟨79367, 5, [(2, 1), (7, 1), (5669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5669
  · decide +kernel

theorem prime_85751 : Nat.Prime 85751 := by
  apply nodeValid_prime [2, 5, 7] ⟨85751, 14, [(2, 1), (5, 3), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_89891 : Nat.Prime 89891 := by
  apply nodeValid_prime [2, 5, 89, 101] ⟨89891, 7, [(2, 1), (5, 1), (89, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_101
  · decide +kernel

theorem prime_96517 : Nat.Prime 96517 := by
  apply nodeValid_prime [2, 3, 7, 383] ⟨96517, 2, [(2, 2), (3, 2), (7, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
  · decide +kernel

theorem prime_97553 : Nat.Prime 97553 := by
  apply nodeValid_prime [2, 7, 13, 67] ⟨97553, 3, [(2, 4), (7, 1), (13, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_117839 : Nat.Prime 117839 := by
  apply nodeValid_prime [2, 7, 19, 443] ⟨117839, 7, [(2, 1), (7, 1), (19, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_443
  · decide +kernel

theorem prime_118709 : Nat.Prime 118709 := by
  apply nodeValid_prime [2, 59, 503] ⟨118709, 2, [(2, 2), (59, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_503
  · decide +kernel

theorem prime_124351 : Nat.Prime 124351 := by
  apply nodeValid_prime [2, 3, 5, 829] ⟨124351, 6, [(2, 1), (3, 1), (5, 2), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_829
  · decide +kernel

theorem prime_152839 : Nat.Prime 152839 := by
  apply nodeValid_prime [2, 3, 7, 1213] ⟨152839, 3, [(2, 1), (3, 2), (7, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1213
  · decide +kernel

theorem prime_153191 : Nat.Prime 153191 := by
  apply nodeValid_prime [2, 5, 15319] ⟨153191, 11, [(2, 1), (5, 1), (15319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15319
  · decide +kernel

theorem prime_163733 : Nat.Prime 163733 := by
  apply nodeValid_prime [2, 40933] ⟨163733, 2, [(2, 2), (40933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40933
  · decide +kernel

theorem prime_172801 : Nat.Prime 172801 := by
  apply nodeValid_prime [2, 3, 5] ⟨172801, 7, [(2, 8), (3, 3), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_176747 : Nat.Prime 176747 := by
  apply nodeValid_prime [2, 67, 1319] ⟨176747, 2, [(2, 1), (67, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_1319
  · decide +kernel

theorem prime_221953 : Nat.Prime 221953 := by
  apply nodeValid_prime [2, 3, 17] ⟨221953, 10, [(2, 8), (3, 1), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_229753 : Nat.Prime 229753 := by
  apply nodeValid_prime [2, 3, 3191] ⟨229753, 11, [(2, 3), (3, 2), (3191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3191
  · decide +kernel

theorem prime_235679 : Nat.Prime 235679 := by
  apply nodeValid_prime [2, 117839] ⟨235679, 11, [(2, 1), (117839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117839
  · decide +kernel

theorem prime_240049 : Nat.Prime 240049 := by
  apply nodeValid_prime [2, 3, 1667] ⟨240049, 7, [(2, 4), (3, 2), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1667
  · decide +kernel

theorem prime_259411 : Nat.Prime 259411 := by
  apply nodeValid_prime [2, 3, 5, 8647] ⟨259411, 2, [(2, 1), (3, 1), (5, 1), (8647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8647
  · decide +kernel

theorem prime_265117 : Nat.Prime 265117 := by
  apply nodeValid_prime [2, 3, 22093] ⟨265117, 2, [(2, 2), (3, 1), (22093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22093
  · decide +kernel

theorem prime_316097 : Nat.Prime 316097 := by
  apply nodeValid_prime [2, 11, 449] ⟨316097, 3, [(2, 6), (11, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_449
  · decide +kernel

theorem prime_320107 : Nat.Prime 320107 := by
  apply nodeValid_prime [2, 3, 31, 1721] ⟨320107, 2, [(2, 1), (3, 1), (31, 1), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1721
  · decide +kernel

theorem prime_372769 : Nat.Prime 372769 := by
  apply nodeValid_prime [2, 3, 11, 353] ⟨372769, 17, [(2, 5), (3, 1), (11, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_353
  · decide +kernel

theorem prime_410513 : Nat.Prime 410513 := by
  apply nodeValid_prime [2, 25657] ⟨410513, 3, [(2, 4), (25657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25657
  · decide +kernel

theorem prime_504991 : Nat.Prime 504991 := by
  apply nodeValid_prime [2, 3, 5, 31, 181] ⟨504991, 6, [(2, 1), (3, 2), (5, 1), (31, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_181
  · decide +kernel

theorem prime_507781 : Nat.Prime 507781 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 31] ⟨507781, 6, [(2, 2), (3, 2), (5, 1), (7, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_547909 : Nat.Prime 547909 := by
  apply nodeValid_prime [2, 3, 45659] ⟨547909, 6, [(2, 2), (3, 1), (45659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45659
  · decide +kernel

theorem prime_760079 : Nat.Prime 760079 := by
  apply nodeValid_prime [2, 11, 34549] ⟨760079, 11, [(2, 1), (11, 1), (34549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_34549
  · decide +kernel

theorem prime_907589 : Nat.Prime 907589 := by
  apply nodeValid_prime [2, 11, 20627] ⟨907589, 2, [(2, 2), (11, 1), (20627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_20627
  · decide +kernel

theorem prime_949673 : Nat.Prime 949673 := by
  apply nodeValid_prime [2, 118709] ⟨949673, 3, [(2, 3), (118709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_118709
  · decide +kernel

theorem prime_965171 : Nat.Prime 965171 := by
  apply nodeValid_prime [2, 5, 96517] ⟨965171, 6, [(2, 1), (5, 1), (96517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_96517
  · decide +kernel

theorem prime_1125599 : Nat.Prime 1125599 := by
  apply nodeValid_prime [2, 19, 1559] ⟨1125599, 13, [(2, 1), (19, 2), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1559
  · decide +kernel

theorem prime_1199623 : Nat.Prime 1199623 := by
  apply nodeValid_prime [2, 3, 17, 19, 619] ⟨1199623, 3, [(2, 1), (3, 1), (17, 1), (19, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_619
  · decide +kernel

theorem prime_1221533 : Nat.Prime 1221533 := by
  apply nodeValid_prime [2, 13, 139] ⟨1221533, 2, [(2, 2), (13, 3), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_139
  · decide +kernel

theorem prime_1282909 : Nat.Prime 1282909 := by
  apply nodeValid_prime [2, 3, 11, 9719] ⟨1282909, 30, [(2, 2), (3, 1), (11, 1), (9719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9719
  · decide +kernel

theorem prime_1284583 : Nat.Prime 1284583 := by
  apply nodeValid_prime [2, 3, 13, 43, 383] ⟨1284583, 6, [(2, 1), (3, 1), (13, 1), (43, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_383
  · decide +kernel

theorem prime_1489451 : Nat.Prime 1489451 := by
  apply nodeValid_prime [2, 5, 29789] ⟨1489451, 2, [(2, 1), (5, 2), (29789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29789
  · decide +kernel

theorem prime_1624969 : Nat.Prime 1624969 := by
  apply nodeValid_prime [2, 3, 7523] ⟨1624969, 14, [(2, 3), (3, 3), (7523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7523
  · decide +kernel

theorem prime_1652897 : Nat.Prime 1652897 := by
  apply nodeValid_prime [2, 7, 47, 157] ⟨1652897, 3, [(2, 5), (7, 1), (47, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_157
  · decide +kernel

theorem prime_1815179 : Nat.Prime 1815179 := by
  apply nodeValid_prime [2, 907589] ⟨1815179, 2, [(2, 1), (907589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_907589
  · decide +kernel

theorem prime_1993261 : Nat.Prime 1993261 := by
  apply nodeValid_prime [2, 3, 5, 139, 239] ⟨1993261, 6, [(2, 2), (3, 1), (5, 1), (139, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_239
  · decide +kernel

theorem prime_2356831 : Nat.Prime 2356831 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 43] ⟨2356831, 6, [(2, 1), (3, 3), (5, 1), (7, 1), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_3900367 : Nat.Prime 3900367 := by
  apply nodeValid_prime [2, 3, 72229] ⟨3900367, 6, [(2, 1), (3, 3), (72229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_72229
  · decide +kernel

theorem prime_4249123 : Nat.Prime 4249123 := by
  apply nodeValid_prime [2, 3, 19, 37273] ⟨4249123, 2, [(2, 1), (3, 1), (19, 1), (37273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37273
  · decide +kernel

theorem prime_5049911 : Nat.Prime 5049911 := by
  apply nodeValid_prime [2, 5, 504991] ⟨5049911, 11, [(2, 1), (5, 1), (504991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_504991
  · decide +kernel

theorem prime_5138333 : Nat.Prime 5138333 := by
  apply nodeValid_prime [2, 1284583] ⟨5138333, 2, [(2, 2), (1284583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1284583
  · decide +kernel

theorem prime_5154101 : Nat.Prime 5154101 := by
  apply nodeValid_prime [2, 5, 7, 37, 199] ⟨5154101, 11, [(2, 2), (5, 2), (7, 1), (37, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_199
  · decide +kernel

theorem prime_5273753 : Nat.Prime 5273753 := by
  apply nodeValid_prime [2, 11, 59929] ⟨5273753, 3, [(2, 3), (11, 1), (59929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59929
  · decide +kernel

theorem prime_5479091 : Nat.Prime 5479091 := by
  apply nodeValid_prime [2, 5, 547909] ⟨5479091, 2, [(2, 1), (5, 1), (547909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_547909
  · decide +kernel

theorem prime_7752229 : Nat.Prime 7752229 := by
  apply nodeValid_prime [2, 3, 11, 19, 281] ⟨7752229, 2, [(2, 2), (3, 1), (11, 2), (19, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_281
  · decide +kernel

theorem prime_9295303 : Nat.Prime 9295303 := by
  apply nodeValid_prime [2, 3, 61, 109, 233] ⟨9295303, 3, [(2, 1), (3, 1), (61, 1), (109, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_109
    · exact prime_233
  · decide +kernel

theorem prime_10949483 : Nat.Prime 10949483 := by
  apply nodeValid_prime [2, 53, 1949] ⟨10949483, 2, [(2, 1), (53, 2), (1949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1949
  · decide +kernel

theorem prime_11847607 : Nat.Prime 11847607 := by
  apply nodeValid_prime [2, 3, 17, 41, 2833] ⟨11847607, 5, [(2, 1), (3, 1), (17, 1), (41, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_2833
  · decide +kernel

theorem prime_11915609 : Nat.Prime 11915609 := by
  apply nodeValid_prime [2, 1489451] ⟨11915609, 3, [(2, 3), (1489451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1489451
  · decide +kernel

theorem prime_12459457 : Nat.Prime 12459457 := by
  apply nodeValid_prime [2, 3, 97, 223] ⟨12459457, 7, [(2, 6), (3, 2), (97, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_223
  · decide +kernel

theorem prime_12740573 : Nat.Prime 12740573 := by
  apply nodeValid_prime [2, 13, 47, 401] ⟨12740573, 2, [(2, 2), (13, 2), (47, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_401
  · decide +kernel

theorem prime_15776143 : Nat.Prime 15776143 := by
  apply nodeValid_prime [2, 3, 79, 83, 401] ⟨15776143, 3, [(2, 1), (3, 1), (79, 1), (83, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_83
    · exact prime_401
  · decide +kernel

theorem prime_16106777 : Nat.Prime 16106777 := by
  apply nodeValid_prime [2, 7, 71, 4051] ⟨16106777, 3, [(2, 3), (7, 1), (71, 1), (4051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_4051
  · decide +kernel

theorem prime_19292993 : Nat.Prime 19292993 := by
  apply nodeValid_prime [2, 487, 619] ⟨19292993, 3, [(2, 6), (487, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_619
  · decide +kernel

theorem prime_23881859 : Nat.Prime 23881859 := by
  apply nodeValid_prime [2, 7, 11, 13, 79, 151] ⟨23881859, 2, [(2, 1), (7, 1), (11, 1), (13, 1), (79, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_79
    · exact prime_151
  · decide +kernel

theorem prime_25942361 : Nat.Prime 25942361 := by
  apply nodeValid_prime [2, 5, 269, 2411] ⟨25942361, 3, [(2, 3), (5, 1), (269, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_2411
  · decide +kernel

theorem prime_32681377 : Nat.Prime 32681377 := by
  apply nodeValid_prime [2, 3, 7, 13, 29, 43] ⟨32681377, 15, [(2, 5), (3, 2), (7, 1), (13, 1), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_39669529 : Nat.Prime 39669529 := by
  apply nodeValid_prime [2, 3, 1652897] ⟨39669529, 17, [(2, 3), (3, 1), (1652897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1652897
  · decide +kernel

theorem prime_42422959 : Nat.Prime 42422959 := by
  apply nodeValid_prime [2, 3, 2356831] ⟨42422959, 3, [(2, 1), (3, 2), (2356831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2356831
  · decide +kernel

theorem prime_50709677 : Nat.Prime 50709677 := by
  apply nodeValid_prime [2, 31, 101, 4049] ⟨50709677, 2, [(2, 2), (31, 1), (101, 1), (4049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_101
    · exact prime_4049
  · decide +kernel

theorem prime_64861807 : Nat.Prime 64861807 := by
  apply nodeValid_prime [2, 3, 29, 372769] ⟨64861807, 3, [(2, 1), (3, 1), (29, 1), (372769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_372769
  · decide +kernel

theorem prime_89440397 : Nat.Prime 89440397 := by
  apply nodeValid_prime [2, 37, 61, 9907] ⟨89440397, 2, [(2, 2), (37, 1), (61, 1), (9907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_61
    · exact prime_9907
  · decide +kernel

theorem prime_93490217 : Nat.Prime 93490217 := by
  apply nodeValid_prime [2, 23, 103, 4933] ⟨93490217, 3, [(2, 3), (23, 1), (103, 1), (4933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_103
    · exact prime_4933
  · decide +kernel

theorem prime_96176753 : Nat.Prime 96176753 := by
  apply nodeValid_prime [2, 7, 17, 50513] ⟨96176753, 5, [(2, 4), (7, 1), (17, 1), (50513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_50513
  · decide +kernel

theorem prime_118406201 : Nat.Prime 118406201 := by
  apply nodeValid_prime [2, 5, 11, 107, 503] ⟨118406201, 3, [(2, 3), (5, 2), (11, 1), (107, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_107
    · exact prime_503
  · decide +kernel

theorem prime_131783797 : Nat.Prime 131783797 := by
  apply nodeValid_prime [2, 3, 17, 349, 617] ⟨131783797, 2, [(2, 2), (3, 2), (17, 1), (349, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_349
    · exact prime_617
  · decide +kernel

theorem prime_137004337 : Nat.Prime 137004337 := by
  apply nodeValid_prime [2, 3, 7, 199, 683] ⟨137004337, 10, [(2, 4), (3, 2), (7, 1), (199, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199
    · exact prime_683
  · decide +kernel

theorem prime_162276427 : Nat.Prime 162276427 := by
  apply nodeValid_prime [2, 3, 13, 271, 853] ⟨162276427, 3, [(2, 1), (3, 3), (13, 1), (271, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_271
    · exact prime_853
  · decide +kernel

theorem prime_169343989 : Nat.Prime 169343989 := by
  apply nodeValid_prime [2, 3, 11, 1282909] ⟨169343989, 2, [(2, 2), (3, 1), (11, 1), (1282909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1282909
  · decide +kernel

theorem prime_189100633 : Nat.Prime 189100633 := by
  apply nodeValid_prime [2, 3, 7, 1125599] ⟨189100633, 5, [(2, 3), (3, 1), (7, 1), (1125599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1125599
  · decide +kernel

theorem prime_207538889 : Nat.Prime 207538889 := by
  apply nodeValid_prime [2, 25942361] ⟨207538889, 3, [(2, 3), (25942361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25942361
  · decide +kernel

theorem prime_276904451 : Nat.Prime 276904451 := by
  apply nodeValid_prime [2, 5, 127, 43607] ⟨276904451, 2, [(2, 1), (5, 2), (127, 1), (43607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_43607
  · decide +kernel

theorem prime_423572509 : Nat.Prime 423572509 := by
  apply nodeValid_prime [2, 3, 23, 173, 2957] ⟨423572509, 6, [(2, 2), (3, 2), (23, 1), (173, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_173
    · exact prime_2957
  · decide +kernel

theorem prime_513026389 : Nat.Prime 513026389 := by
  apply nodeValid_prime [2, 3, 7, 157, 12967] ⟨513026389, 2, [(2, 2), (3, 2), (7, 1), (157, 1), (12967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
    · exact prime_12967
  · decide +kernel

theorem prime_808576127 : Nat.Prime 808576127 := by
  apply nodeValid_prime [2, 1279, 316097] ⟨808576127, 5, [(2, 1), (1279, 1), (316097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1279
    · exact prime_316097
  · decide +kernel

theorem prime_864793217 : Nat.Prime 864793217 := by
  apply nodeValid_prime [2, 7, 965171] ⟨864793217, 3, [(2, 7), (7, 1), (965171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_965171
  · decide +kernel

theorem prime_1210363457 : Nat.Prime 1210363457 := by
  apply nodeValid_prime [2, 107, 176747] ⟨1210363457, 3, [(2, 6), (107, 1), (176747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_176747
  · decide +kernel

theorem prime_1470882113 : Nat.Prime 1470882113 := by
  apply nodeValid_prime [2, 7, 19, 172801] ⟨1470882113, 3, [(2, 6), (7, 1), (19, 1), (172801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_172801
  · decide +kernel

theorem prime_1528439659 : Nat.Prime 1528439659 := by
  apply nodeValid_prime [2, 3, 181, 421, 3343] ⟨1528439659, 2, [(2, 1), (3, 1), (181, 1), (421, 1), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_421
    · exact prime_3343
  · decide +kernel

theorem prime_1776217939 : Nat.Prime 1776217939 := by
  apply nodeValid_prime [2, 3, 11, 53, 507781] ⟨1776217939, 3, [(2, 1), (3, 1), (11, 1), (53, 1), (507781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_507781
  · decide +kernel

theorem prime_1902317243 : Nat.Prime 1902317243 := by
  apply nodeValid_prime [2, 7, 331, 410513] ⟨1902317243, 6, [(2, 1), (7, 1), (331, 1), (410513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_331
    · exact prime_410513
  · decide +kernel

theorem prime_2825332787 : Nat.Prime 2825332787 := by
  apply nodeValid_prime [2, 4423, 319391] ⟨2825332787, 2, [(2, 1), (4423, 1), (319391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4423
    · exact prime_319391
  · decide +kernel

theorem prime_3671435819 : Nat.Prime 3671435819 := by
  apply nodeValid_prime [2, 1933, 949673] ⟨3671435819, 2, [(2, 1), (1933, 1), (949673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1933
    · exact prime_949673
  · decide +kernel

theorem prime_4140421013 : Nat.Prime 4140421013 := by
  apply nodeValid_prime [2, 7, 13, 1624969] ⟨4140421013, 3, [(2, 2), (7, 2), (13, 1), (1624969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1624969
  · decide +kernel

theorem prime_8577098869 : Nat.Prime 8577098869 := by
  apply nodeValid_prime [2, 3, 13, 2017, 27259] ⟨8577098869, 2, [(2, 2), (3, 1), (13, 1), (2017, 1), (27259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2017
    · exact prime_27259
  · decide +kernel

theorem prime_9530756423 : Nat.Prime 9530756423 := by
  apply nodeValid_prime [2, 11, 23, 233, 7349] ⟨9530756423, 5, [(2, 1), (11, 2), (23, 1), (233, 1), (7349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_233
    · exact prime_7349
  · decide +kernel

theorem prime_12155644783 : Nat.Prime 12155644783 := by
  apply nodeValid_prime [2, 3, 19, 11847607] ⟨12155644783, 3, [(2, 1), (3, 3), (19, 1), (11847607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11847607
  · decide +kernel

theorem prime_17760930151 : Nat.Prime 17760930151 := by
  apply nodeValid_prime [2, 3, 5, 118406201] ⟨17760930151, 15, [(2, 1), (3, 1), (5, 2), (118406201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_118406201
  · decide +kernel

theorem prime_25372757369 : Nat.Prime 25372757369 := by
  apply nodeValid_prime [2, 7, 1709, 265117] ⟨25372757369, 3, [(2, 3), (7, 1), (1709, 1), (265117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1709
    · exact prime_265117
  · decide +kernel

theorem prime_29371486553 : Nat.Prime 29371486553 := by
  apply nodeValid_prime [2, 3671435819] ⟨29371486553, 3, [(2, 3), (3671435819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3671435819
  · decide +kernel

theorem prime_31132555813 : Nat.Prime 31132555813 := by
  apply nodeValid_prime [2, 3, 864793217] ⟨31132555813, 2, [(2, 2), (3, 2), (864793217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_864793217
  · decide +kernel

theorem prime_36873937141 : Nat.Prime 36873937141 := by
  apply nodeValid_prime [2, 3, 5, 4021, 152839] ⟨36873937141, 6, [(2, 2), (3, 1), (5, 1), (4021, 1), (152839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4021
    · exact prime_152839
  · decide +kernel

theorem prime_45030193177 : Nat.Prime 45030193177 := by
  apply nodeValid_prime [2, 3, 37, 50709677] ⟨45030193177, 5, [(2, 3), (3, 1), (37, 1), (50709677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_50709677
  · decide +kernel

theorem prime_58845013391 : Nat.Prime 58845013391 := by
  apply nodeValid_prime [2, 5, 373, 15776143] ⟨58845013391, 13, [(2, 1), (5, 1), (373, 1), (15776143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_373
    · exact prime_15776143
  · decide +kernel

theorem prime_59305680983 : Nat.Prime 59305680983 := by
  apply nodeValid_prime [2, 127, 131, 349, 5107] ⟨59305680983, 5, [(2, 1), (127, 1), (131, 1), (349, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_131
    · exact prime_349
    · exact prime_5107
  · decide +kernel

theorem prime_67780353593 : Nat.Prime 67780353593 := by
  apply nodeValid_prime [2, 7, 1210363457] ⟨67780353593, 3, [(2, 3), (7, 1), (1210363457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1210363457
  · decide +kernel

theorem prime_118508750929 : Nat.Prime 118508750929 := by
  apply nodeValid_prime [2, 3, 211, 3900367] ⟨118508750929, 11, [(2, 4), (3, 2), (211, 1), (3900367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_3900367
  · decide +kernel

theorem prime_135560707187 : Nat.Prime 135560707187 := by
  apply nodeValid_prime [2, 67780353593] ⟨135560707187, 2, [(2, 1), (67780353593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67780353593
  · decide +kernel

theorem prime_198199260041 : Nat.Prime 198199260041 := by
  apply nodeValid_prime [2, 5, 53, 93490217] ⟨198199260041, 3, [(2, 3), (5, 1), (53, 1), (93490217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_93490217
  · decide +kernel

theorem prime_294225068623 : Nat.Prime 294225068623 := by
  apply nodeValid_prime [2, 3, 153191, 320107] ⟨294225068623, 6, [(2, 1), (3, 1), (153191, 1), (320107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_153191
    · exact prime_320107
  · decide +kernel

theorem prime_353070080347 : Nat.Prime 353070080347 := by
  apply nodeValid_prime [2, 3, 58845013391] ⟨353070080347, 2, [(2, 1), (3, 1), (58845013391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58845013391
  · decide +kernel

theorem prime_879615767323 : Nat.Prime 879615767323 := by
  apply nodeValid_prime [2, 3, 4463, 10949483] ⟨879615767323, 2, [(2, 1), (3, 2), (4463, 1), (10949483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4463
    · exact prime_10949483
  · decide +kernel

theorem prime_1776093015101 : Nat.Prime 1776093015101 := by
  apply nodeValid_prime [2, 5, 17760930151] ⟨1776093015101, 2, [(2, 2), (5, 2), (17760930151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17760930151
  · decide +kernel

theorem prime_3500160496199 : Nat.Prime 3500160496199 := by
  apply nodeValid_prime [2, 17, 1151, 89440397] ⟨3500160496199, 11, [(2, 1), (17, 1), (1151, 1), (89440397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1151
    · exact prime_89440397
  · decide +kernel

theorem prime_3500160498269 : Nat.Prime 3500160498269 := by
  apply nodeValid_prime [2, 7, 79, 127, 12459457] ⟨3500160498269, 2, [(2, 2), (7, 1), (79, 1), (127, 1), (12459457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_127
    · exact prime_12459457
  · decide +kernel

theorem prime_3500160502939 : Nat.Prime 3500160502939 := by
  apply nodeValid_prime [2, 3, 11, 10321, 5138333] ⟨3500160502939, 10, [(2, 1), (3, 1), (11, 1), (10321, 1), (5138333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_10321
    · exact prime_5138333
  · decide +kernel

theorem prime_3503206452817 : Nat.Prime 3503206452817 := by
  apply nodeValid_prime [2, 3, 7, 659, 5273753] ⟨3503206452817, 10, [(2, 4), (3, 2), (7, 1), (659, 1), (5273753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_659
    · exact prime_5273753
  · decide +kernel

theorem prime_3503206453601 : Nat.Prime 3503206453601 := by
  apply nodeValid_prime [2, 5, 7, 7933, 78857] ⟨3503206453601, 3, [(2, 5), (5, 2), (7, 1), (7933, 1), (78857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7933
    · exact prime_78857
  · decide +kernel

theorem prime_3503206453843 : Nat.Prime 3503206453843 := by
  apply nodeValid_prime [2, 3, 163, 281, 4249123] ⟨3503206453843, 13, [(2, 1), (3, 2), (163, 1), (281, 1), (4249123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_281
    · exact prime_4249123
  · decide +kernel

theorem prime_3506254205521 : Nat.Prime 3506254205521 := by
  apply nodeValid_prime [2, 3, 5, 11, 263, 5049911] ⟨3506254205521, 17, [(2, 4), (3, 1), (5, 1), (11, 1), (263, 1), (5049911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_263
    · exact prime_5049911
  · decide +kernel

theorem prime_3506254211587 : Nat.Prime 3506254211587 := by
  apply nodeValid_prime [2, 3, 7, 47, 1776217939] ⟨3506254211587, 2, [(2, 1), (3, 1), (7, 1), (47, 1), (1776217939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_1776217939
  · decide +kernel

theorem prime_3506254212823 : Nat.Prime 3506254212823 := by
  apply nodeValid_prime [2, 3, 17881, 32681377] ⟨3506254212823, 3, [(2, 1), (3, 1), (17881, 1), (32681377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17881
    · exact prime_32681377
  · decide +kernel

theorem prime_3509303672477 : Nat.Prime 3509303672477 := by
  apply nodeValid_prime [2, 7, 24317, 5154101] ⟨3509303672477, 2, [(2, 2), (7, 1), (24317, 1), (5154101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_24317
    · exact prime_5154101
  · decide +kernel

theorem prime_3509303674937 : Nat.Prime 3509303674937 := by
  apply nodeValid_prime [2, 59, 31547, 235679] ⟨3509303674937, 3, [(2, 3), (59, 1), (31547, 1), (235679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_31547
    · exact prime_235679
  · decide +kernel

theorem prime_3509303737003 : Nat.Prime 3509303737003 := by
  apply nodeValid_prime [2, 3, 7, 37, 43, 3469, 15139] ⟨3509303737003, 3, [(2, 1), (3, 1), (7, 1), (37, 1), (43, 1), (3469, 1), (15139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_43
    · exact prime_3469
    · exact prime_15139
  · decide +kernel

theorem prime_3512355067807 : Nat.Prime 3512355067807 := by
  apply nodeValid_prime [2, 3, 13, 45030193177] ⟨3512355067807, 3, [(2, 1), (3, 1), (13, 1), (45030193177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_45030193177
  · decide +kernel

theorem prime_3512355155669 : Nat.Prime 3512355155669 := by
  apply nodeValid_prime [2, 17, 83, 7841, 79367] ⟨3512355155669, 2, [(2, 2), (17, 1), (83, 1), (7841, 1), (79367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_83
    · exact prime_7841
    · exact prime_79367
  · decide +kernel

theorem prime_3512355157343 : Nat.Prime 3512355157343 := by
  apply nodeValid_prime [2, 37, 251, 189100633] ⟨3512355157343, 5, [(2, 1), (37, 1), (251, 1), (189100633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_251
    · exact prime_189100633
  · decide +kernel

theorem prime_3515408199409 : Nat.Prime 3515408199409 := by
  apply nodeValid_prime [2, 3, 7, 43, 179, 193, 7043] ⟨3515408199409, 11, [(2, 4), (3, 1), (7, 1), (43, 1), (179, 1), (193, 1), (7043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_179
    · exact prime_193
    · exact prime_7043
  · decide +kernel

theorem prime_3515408248321 : Nat.Prime 3515408248321 := by
  apply nodeValid_prime [2, 3, 5, 29, 2087, 2521] ⟨3515408248321, 11, [(2, 9), (3, 2), (5, 1), (29, 1), (2087, 1), (2521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_2087
    · exact prime_2521
  · decide +kernel

theorem prime_3515408250071 : Nat.Prime 3515408250071 := by
  apply nodeValid_prime [2, 5, 239, 1470882113] ⟨3515408250071, 11, [(2, 1), (5, 1), (239, 1), (1470882113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_1470882113
  · decide +kernel

theorem prime_3518463068803 : Nat.Prime 3518463068803 := by
  apply nodeValid_prime [2, 3, 11, 14813, 1199623] ⟨3518463068803, 2, [(2, 1), (3, 2), (11, 1), (14813, 1), (1199623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_14813
    · exact prime_1199623
  · decide +kernel

theorem prime_3518463069293 : Nat.Prime 3518463069293 := by
  apply nodeValid_prime [2, 879615767323] ⟨3518463069293, 2, [(2, 2), (879615767323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_879615767323
  · decide +kernel

theorem prime_3518463133411 : Nat.Prime 3518463133411 := by
  apply nodeValid_prime [2, 3, 5, 6079, 19292993] ⟨3518463133411, 2, [(2, 1), (3, 1), (5, 1), (6079, 1), (19292993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6079
    · exact prime_19292993
  · decide +kernel

theorem prime_3521519858347 : Nat.Prime 3521519858347 := by
  apply nodeValid_prime [2, 3, 7, 6581, 12740573] ⟨3521519858347, 3, [(2, 1), (3, 1), (7, 1), (6581, 1), (12740573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6581
    · exact prime_12740573
  · decide +kernel

theorem prime_3521519867161 : Nat.Prime 3521519867161 := by
  apply nodeValid_prime [2, 3, 5, 17, 317, 1815179] ⟨3521519867161, 22, [(2, 3), (3, 2), (5, 1), (17, 1), (317, 1), (1815179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_317
    · exact prime_1815179
  · decide +kernel

theorem prime_3521519868553 : Nat.Prime 3521519868553 := by
  apply nodeValid_prime [2, 3, 7, 101, 207538889] ⟨3521519868553, 5, [(2, 3), (3, 1), (7, 1), (101, 1), (207538889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
    · exact prime_207538889
  · decide +kernel

theorem prime_3524578381589 : Nat.Prime 3524578381589 := by
  apply nodeValid_prime [2, 11, 29, 97, 229, 124351] ⟨3524578381589, 2, [(2, 2), (11, 1), (29, 1), (97, 1), (229, 1), (124351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_97
    · exact prime_229
    · exact prime_124351
  · decide +kernel

theorem prime_3524578386361 : Nat.Prime 3524578386361 := by
  apply nodeValid_prime [2, 3, 5, 29371486553] ⟨3524578386361, 11, [(2, 3), (3, 1), (5, 1), (29371486553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29371486553
  · decide +kernel

theorem prime_3524578386863 : Nat.Prime 3524578386863 := by
  apply nodeValid_prime [2, 13, 135560707187] ⟨3524578386863, 5, [(2, 1), (13, 1), (135560707187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_135560707187
  · decide +kernel

theorem prime_3527638703077 : Nat.Prime 3527638703077 := by
  apply nodeValid_prime [2, 3, 71, 4140421013] ⟨3527638703077, 2, [(2, 2), (3, 1), (71, 1), (4140421013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_4140421013
  · decide +kernel

theorem prime_3527638732687 : Nat.Prime 3527638732687 := by
  apply nodeValid_prime [2, 3, 13859, 42422959] ⟨3527638732687, 3, [(2, 1), (3, 1), (13859, 1), (42422959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13859
    · exact prime_42422959
  · decide +kernel

theorem prime_3527638732973 : Nat.Prime 3527638732973 := by
  apply nodeValid_prime [2, 577, 1528439659] ⟨3527638732973, 2, [(2, 2), (577, 1), (1528439659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_1528439659
  · decide +kernel

theorem prime_3530700803009 : Nat.Prime 3530700803009 := by
  apply nodeValid_prime [2, 29, 1902317243] ⟨3530700803009, 3, [(2, 6), (29, 1), (1902317243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1902317243
  · decide +kernel

theorem prime_3530700803471 : Nat.Prime 3530700803471 := by
  apply nodeValid_prime [2, 5, 353070080347] ⟨3530700803471, 7, [(2, 1), (5, 1), (353070080347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_353070080347
  · decide +kernel

theorem prime_3530700823477 : Nat.Prime 3530700823477 := by
  apply nodeValid_prime [2, 3, 294225068623] ⟨3530700823477, 2, [(2, 2), (3, 1), (294225068623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_294225068623
  · decide +kernel

theorem prime_3533764723417 : Nat.Prime 3533764723417 := by
  apply nodeValid_prime [2, 3, 24623, 1993261] ⟨3533764723417, 5, [(2, 3), (3, 2), (24623, 1), (1993261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24623
    · exact prime_1993261
  · decide +kernel

theorem prime_3533764724137 : Nat.Prime 3533764724137 := by
  apply nodeValid_prime [2, 3, 31, 2297, 229753] ⟨3533764724137, 5, [(2, 3), (3, 3), (31, 1), (2297, 1), (229753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2297
    · exact prime_229753
  · decide +kernel

theorem prime_3533764734029 : Nat.Prime 3533764734029 := by
  apply nodeValid_prime [2, 103, 8577098869] ⟨3533764734029, 2, [(2, 2), (103, 1), (8577098869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_8577098869
  · decide +kernel

theorem prime_3536830445587 : Nat.Prime 3536830445587 := by
  apply nodeValid_prime [2, 3, 76039, 7752229] ⟨3536830445587, 3, [(2, 1), (3, 1), (76039, 1), (7752229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76039
    · exact prime_7752229
  · decide +kernel

theorem prime_3536830450151 : Nat.Prime 3536830450151 := by
  apply nodeValid_prime [2, 5, 167, 423572509] ⟨3536830450151, 11, [(2, 1), (5, 2), (167, 1), (423572509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_423572509
  · decide +kernel

theorem prime_3536830450189 : Nat.Prime 3536830450189 := by
  apply nodeValid_prime [2, 3, 7, 487, 3943, 7309] ⟨3536830450189, 6, [(2, 2), (3, 2), (7, 1), (487, 1), (3943, 1), (7309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_487
    · exact prime_3943
    · exact prime_7309
  · decide +kernel

theorem prime_3539897965537 : Nat.Prime 3539897965537 := by
  apply nodeValid_prime [2, 3, 36873937141] ⟨3539897965537, 5, [(2, 5), (3, 1), (36873937141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36873937141
  · decide +kernel

theorem prime_3539897978579 : Nat.Prime 3539897978579 := by
  apply nodeValid_prime [2, 13, 839, 162276427] ⟨3539897978579, 6, [(2, 1), (13, 1), (839, 1), (162276427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_839
    · exact prime_162276427
  · decide +kernel

theorem prime_3539897978833 : Nat.Prime 3539897978833 := by
  apply nodeValid_prime [2, 3, 379, 64861807] ⟨3539897978833, 5, [(2, 4), (3, 2), (379, 1), (64861807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_64861807
  · decide +kernel

theorem prime_3542967289859 : Nat.Prime 3542967289859 := by
  apply nodeValid_prime [2, 41, 101, 4759, 89891] ⟨3542967289859, 2, [(2, 1), (41, 1), (101, 1), (4759, 1), (89891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_101
    · exact prime_4759
    · exact prime_89891
  · decide +kernel

theorem prime_3542967314353 : Nat.Prime 3542967314353 := by
  apply nodeValid_prime [2, 3, 179, 1409, 97553] ⟨3542967314353, 5, [(2, 4), (3, 2), (179, 1), (1409, 1), (97553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_1409
    · exact prime_97553
  · decide +kernel

theorem prime_3542967314899 : Nat.Prime 3542967314899 := by
  apply nodeValid_prime [2, 3, 11, 19, 2825332787] ⟨3542967314899, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (2825332787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_2825332787
  · decide +kernel

theorem prime_3546038399507 : Nat.Prime 3546038399507 := by
  apply nodeValid_prime [2, 19, 337, 276904451] ⟨3546038399507, 2, [(2, 1), (19, 1), (337, 1), (276904451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_337
    · exact prime_276904451
  · decide +kernel

theorem prime_3546038400769 : Nat.Prime 3546038400769 := by
  apply nodeValid_prime [2, 3, 513026389] ⟨3546038400769, 13, [(2, 8), (3, 3), (513026389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_513026389
  · decide +kernel

theorem prime_3546038409677 : Nat.Prime 3546038409677 := by
  apply nodeValid_prime [2, 7, 31, 131783797] ⟨3546038409677, 2, [(2, 2), (7, 1), (31, 2), (131783797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_131783797
  · decide +kernel

theorem prime_3549111321463 : Nat.Prime 3549111321463 := by
  apply nodeValid_prime [2, 3, 7, 499, 169343989] ⟨3549111321463, 3, [(2, 1), (3, 1), (7, 1), (499, 1), (169343989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_499
    · exact prime_169343989
  · decide +kernel

theorem prime_3549111362443 : Nat.Prime 3549111362443 := by
  apply nodeValid_prime [2, 3, 259411, 760079] ⟨3549111362443, 2, [(2, 1), (3, 2), (259411, 1), (760079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_259411
    · exact prime_760079
  · decide +kernel

theorem prime_3549111362683 : Nat.Prime 3549111362683 := by
  apply nodeValid_prime [2, 3, 19, 31132555813] ⟨3549111362683, 14, [(2, 1), (3, 1), (19, 1), (31132555813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31132555813
  · decide +kernel

theorem prime_3552186030203 : Nat.Prime 3552186030203 := by
  apply nodeValid_prime [2, 1776093015101] ⟨3552186030203, 2, [(2, 1), (1776093015101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1776093015101
  · decide +kernel

theorem prime_3552186030209 : Nat.Prime 3552186030209 := by
  apply nodeValid_prime [2, 17, 137, 11915609] ⟨3552186030209, 3, [(2, 7), (17, 1), (137, 1), (11915609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_137
    · exact prime_11915609
  · decide +kernel

theorem prime_3552186031661 : Nat.Prime 3552186031661 := by
  apply nodeValid_prime [2, 5, 7, 25372757369] ⟨3552186031661, 2, [(2, 2), (5, 1), (7, 1), (25372757369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_25372757369
  · decide +kernel

theorem prime_3555262527871 : Nat.Prime 3555262527871 := by
  apply nodeValid_prime [2, 3, 5, 118508750929] ⟨3555262527871, 6, [(2, 1), (3, 1), (5, 1), (118508750929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_118508750929
  · decide +kernel

theorem prime_3555262528039 : Nat.Prime 3555262528039 := by
  apply nodeValid_prime [2, 3, 13, 383, 39669529] ⟨3555262528039, 6, [(2, 1), (3, 2), (13, 1), (383, 1), (39669529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_383
    · exact prime_39669529
  · decide +kernel

theorem prime_3555262545151 : Nat.Prime 3555262545151 := by
  apply nodeValid_prime [2, 3, 5, 173, 137004337] ⟨3555262545151, 3, [(2, 1), (3, 1), (5, 2), (173, 1), (137004337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_137004337
  · decide +kernel

theorem prime_3558340858981 : Nat.Prime 3558340858981 := by
  apply nodeValid_prime [2, 3, 5, 59305680983] ⟨3558340858981, 10, [(2, 2), (3, 1), (5, 1), (59305680983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59305680983
  · decide +kernel

theorem prime_3558340859041 : Nat.Prime 3558340859041 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 5479091] ⟨3558340859041, 21, [(2, 5), (3, 2), (5, 1), (11, 1), (41, 1), (5479091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_5479091
  · decide +kernel

theorem prime_3558340862641 : Nat.Prime 3558340862641 := by
  apply nodeValid_prime [2, 3, 5, 18043, 91303] ⟨3558340862641, 13, [(2, 4), (3, 3), (5, 1), (18043, 1), (91303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18043
    · exact prime_91303
  · decide +kernel

theorem prime_3561420982027 : Nat.Prime 3561420982027 := by
  apply nodeValid_prime [2, 3, 63857, 9295303] ⟨3561420982027, 2, [(2, 1), (3, 1), (63857, 1), (9295303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_63857
    · exact prime_9295303
  · decide +kernel

theorem prime_3561420993623 : Nat.Prime 3561420993623 := by
  apply nodeValid_prime [2, 17, 85751, 1221533] ⟨3561420993623, 5, [(2, 1), (17, 1), (85751, 1), (1221533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_85751
    · exact prime_1221533
  · decide +kernel

theorem prime_3561420993803 : Nat.Prime 3561420993803 := by
  apply nodeValid_prime [2, 7, 163733, 221953] ⟨3561420993803, 2, [(2, 1), (7, 2), (163733, 1), (221953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163733
    · exact prime_221953
  · decide +kernel

theorem prime_3564502819687 : Nat.Prime 3564502819687 := by
  apply nodeValid_prime [2, 3, 29, 71, 96176753] ⟨3564502819687, 3, [(2, 1), (3, 2), (29, 1), (71, 1), (96176753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_71
    · exact prime_96176753
  · decide +kernel

theorem prime_3564502820579 : Nat.Prime 3564502820579 := by
  apply nodeValid_prime [2, 7, 149, 8053, 30313] ⟨3564502820579, 2, [(2, 1), (7, 2), (149, 1), (8053, 1), (30313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_149
    · exact prime_8053
    · exact prime_30313
  · decide +kernel

theorem prime_3564502902203 : Nat.Prime 3564502902203 := by
  apply nodeValid_prime [2, 11, 17, 9530756423] ⟨3564502902203, 2, [(2, 1), (11, 1), (17, 1), (9530756423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_9530756423
  · decide +kernel

theorem prime_3567586633591 : Nat.Prime 3567586633591 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 23, 181, 240049] ⟨3567586633591, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (23, 1), (181, 1), (240049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_23
    · exact prime_181
    · exact prime_240049
  · decide +kernel

theorem prime_3567586678393 : Nat.Prime 3567586678393 := by
  apply nodeValid_prime [2, 3, 11, 839, 16106777] ⟨3567586678393, 5, [(2, 3), (3, 1), (11, 1), (839, 1), (16106777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_839
    · exact prime_16106777
  · decide +kernel

theorem prime_3567586680739 : Nat.Prime 3567586680739 := by
  apply nodeValid_prime [2, 3, 198199260041] ⟨3567586680739, 2, [(2, 1), (3, 2), (198199260041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_198199260041
  · decide +kernel

theorem prime_3570672176833 : Nat.Prime 3570672176833 := by
  apply nodeValid_prime [2, 3, 23, 808576127] ⟨3570672176833, 5, [(2, 6), (3, 1), (23, 1), (808576127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_808576127
  · decide +kernel

theorem prime_3570672266527 : Nat.Prime 3570672266527 := by
  apply nodeValid_prime [2, 3, 24919, 23881859] ⟨3570672266527, 3, [(2, 1), (3, 1), (24919, 1), (23881859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24919
    · exact prime_23881859
  · decide +kernel

theorem prime_3570672268357 : Nat.Prime 3570672268357 := by
  apply nodeValid_prime [2, 3, 103, 167, 521, 33203] ⟨3570672268357, 5, [(2, 2), (3, 1), (103, 1), (167, 1), (521, 1), (33203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_167
    · exact prime_521
    · exact prime_33203
  · decide +kernel

theorem prime_3573759522677 : Nat.Prime 3573759522677 := by
  apply nodeValid_prime [2, 7, 23, 419, 439, 30169] ⟨3573759522677, 2, [(2, 2), (7, 1), (23, 1), (419, 1), (439, 1), (30169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_419
    · exact prime_439
    · exact prime_30169
  · decide +kernel

theorem prime_3573759566203 : Nat.Prime 3573759566203 := by
  apply nodeValid_prime [2, 3, 7, 12155644783] ⟨3573759566203, 13, [(2, 1), (3, 1), (7, 2), (12155644783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12155644783
  · decide +kernel

end Sude.Lucas.Generated
