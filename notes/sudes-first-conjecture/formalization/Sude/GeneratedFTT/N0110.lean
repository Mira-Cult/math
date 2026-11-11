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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0107

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9497 : Nat.Prime 9497 := by
  apply nodeValid_prime [2, 1187] ⟨9497, 3, [(2, 3), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1187
  · decide +kernel

theorem prime_13033 : Nat.Prime 13033 := by
  apply nodeValid_prime [2, 3, 181] ⟨13033, 5, [(2, 3), (3, 2), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
  · decide +kernel

theorem prime_14557 : Nat.Prime 14557 := by
  apply nodeValid_prime [2, 3, 1213] ⟨14557, 2, [(2, 2), (3, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1213
  · decide +kernel

theorem prime_15443 : Nat.Prime 15443 := by
  apply nodeValid_prime [2, 7, 1103] ⟨15443, 2, [(2, 1), (7, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1103
  · decide +kernel

theorem prime_16069 : Nat.Prime 16069 := by
  apply nodeValid_prime [2, 3, 13, 103] ⟨16069, 2, [(2, 2), (3, 1), (13, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_103
  · decide +kernel

theorem prime_20981 : Nat.Prime 20981 := by
  apply nodeValid_prime [2, 5, 1049] ⟨20981, 2, [(2, 2), (5, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1049
  · decide +kernel

theorem prime_21481 : Nat.Prime 21481 := by
  apply nodeValid_prime [2, 3, 5, 179] ⟨21481, 13, [(2, 3), (3, 1), (5, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
  · decide +kernel

theorem prime_22901 : Nat.Prime 22901 := by
  apply nodeValid_prime [2, 5, 229] ⟨22901, 2, [(2, 2), (5, 2), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
  · decide +kernel

theorem prime_25373 : Nat.Prime 25373 := by
  apply nodeValid_prime [2, 6343] ⟨25373, 2, [(2, 2), (6343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6343
  · decide +kernel

theorem prime_26021 : Nat.Prime 26021 := by
  apply nodeValid_prime [2, 5, 1301] ⟨26021, 2, [(2, 2), (5, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1301
  · decide +kernel

theorem prime_28837 : Nat.Prime 28837 := by
  apply nodeValid_prime [2, 3, 89] ⟨28837, 2, [(2, 2), (3, 4), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_30689 : Nat.Prime 30689 := by
  apply nodeValid_prime [2, 7, 137] ⟨30689, 3, [(2, 5), (7, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_34981 : Nat.Prime 34981 := by
  apply nodeValid_prime [2, 3, 5, 11, 53] ⟨34981, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_52433 : Nat.Prime 52433 := by
  apply nodeValid_prime [2, 29, 113] ⟨52433, 3, [(2, 4), (29, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_113
  · decide +kernel

theorem prime_54419 : Nat.Prime 54419 := by
  apply nodeValid_prime [2, 7, 13, 23] ⟨54419, 2, [(2, 1), (7, 1), (13, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_59387 : Nat.Prime 59387 := by
  apply nodeValid_prime [2, 23, 1291] ⟨59387, 2, [(2, 1), (23, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1291
  · decide +kernel

theorem prime_61379 : Nat.Prime 61379 := by
  apply nodeValid_prime [2, 30689] ⟨61379, 2, [(2, 1), (30689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30689
  · decide +kernel

theorem prime_68501 : Nat.Prime 68501 := by
  apply nodeValid_prime [2, 5, 137] ⟨68501, 3, [(2, 2), (5, 3), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_96199 : Nat.Prime 96199 := by
  apply nodeValid_prime [2, 3, 16033] ⟨96199, 3, [(2, 1), (3, 1), (16033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16033
  · decide +kernel

theorem prime_99667 : Nat.Prime 99667 := by
  apply nodeValid_prime [2, 3, 7, 113] ⟨99667, 2, [(2, 1), (3, 2), (7, 2), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_103651 : Nat.Prime 103651 := by
  apply nodeValid_prime [2, 3, 5, 691] ⟨103651, 2, [(2, 1), (3, 1), (5, 2), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_691
  · decide +kernel

theorem prime_126631 : Nat.Prime 126631 := by
  apply nodeValid_prime [2, 3, 5, 7, 67] ⟨126631, 6, [(2, 1), (3, 3), (5, 1), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_127081 : Nat.Prime 127081 := by
  apply nodeValid_prime [2, 3, 5, 353] ⟨127081, 7, [(2, 3), (3, 2), (5, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
  · decide +kernel

theorem prime_136447 : Nat.Prime 136447 := by
  apply nodeValid_prime [2, 3, 22741] ⟨136447, 3, [(2, 1), (3, 1), (22741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22741
  · decide +kernel

theorem prime_149251 : Nat.Prime 149251 := by
  apply nodeValid_prime [2, 3, 5, 199] ⟨149251, 2, [(2, 1), (3, 1), (5, 3), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
  · decide +kernel

theorem prime_151549 : Nat.Prime 151549 := by
  apply nodeValid_prime [2, 3, 73, 173] ⟨151549, 2, [(2, 2), (3, 1), (73, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_173
  · decide +kernel

theorem prime_182233 : Nat.Prime 182233 := by
  apply nodeValid_prime [2, 3, 2531] ⟨182233, 5, [(2, 3), (3, 2), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2531
  · decide +kernel

theorem prime_237973 : Nat.Prime 237973 := by
  apply nodeValid_prime [2, 3, 7, 2833] ⟨237973, 6, [(2, 2), (3, 1), (7, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2833
  · decide +kernel

theorem prime_270271 : Nat.Prime 270271 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 13] ⟨270271, 7, [(2, 1), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_344987 : Nat.Prime 344987 := by
  apply nodeValid_prime [2, 181, 953] ⟨344987, 2, [(2, 1), (181, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_953
  · decide +kernel

theorem prime_415201 : Nat.Prime 415201 := by
  apply nodeValid_prime [2, 3, 5, 173] ⟨415201, 11, [(2, 5), (3, 1), (5, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_430999 : Nat.Prime 430999 := by
  apply nodeValid_prime [2, 3, 29, 2477] ⟨430999, 3, [(2, 1), (3, 1), (29, 1), (2477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_2477
  · decide +kernel

theorem prime_464119 : Nat.Prime 464119 := by
  apply nodeValid_prime [2, 3, 103, 751] ⟨464119, 3, [(2, 1), (3, 1), (103, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_751
  · decide +kernel

theorem prime_504461 : Nat.Prime 504461 := by
  apply nodeValid_prime [2, 5, 11, 2293] ⟨504461, 3, [(2, 2), (5, 1), (11, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2293
  · decide +kernel

theorem prime_556289 : Nat.Prime 556289 := by
  apply nodeValid_prime [2, 41, 53] ⟨556289, 3, [(2, 8), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_560767 : Nat.Prime 560767 := by
  apply nodeValid_prime [2, 3, 19, 4919] ⟨560767, 3, [(2, 1), (3, 1), (19, 1), (4919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_4919
  · decide +kernel

theorem prime_573763 : Nat.Prime 573763 := by
  apply nodeValid_prime [2, 3, 7, 19, 719] ⟨573763, 5, [(2, 1), (3, 1), (7, 1), (19, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_719
  · decide +kernel

theorem prime_624031 : Nat.Prime 624031 := by
  apply nodeValid_prime [2, 3, 5, 11, 31, 61] ⟨624031, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (31, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_61
  · decide +kernel

theorem prime_678637 : Nat.Prime 678637 := by
  apply nodeValid_prime [2, 3, 7, 2693] ⟨678637, 2, [(2, 2), (3, 2), (7, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2693
  · decide +kernel

theorem prime_711539 : Nat.Prime 711539 := by
  apply nodeValid_prime [2, 359, 991] ⟨711539, 2, [(2, 1), (359, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_991
  · decide +kernel

theorem prime_731881 : Nat.Prime 731881 := by
  apply nodeValid_prime [2, 3, 5, 19, 107] ⟨731881, 7, [(2, 3), (3, 2), (5, 1), (19, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_107
  · decide +kernel

theorem prime_767881 : Nat.Prime 767881 := by
  apply nodeValid_prime [2, 3, 5, 79] ⟨767881, 31, [(2, 3), (3, 5), (5, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_810401 : Nat.Prime 810401 := by
  apply nodeValid_prime [2, 5, 1013] ⟨810401, 3, [(2, 5), (5, 2), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1013
  · decide +kernel

theorem prime_873331 : Nat.Prime 873331 := by
  apply nodeValid_prime [2, 3, 5, 43, 677] ⟨873331, 2, [(2, 1), (3, 1), (5, 1), (43, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_677
  · decide +kernel

theorem prime_888047 : Nat.Prime 888047 := by
  apply nodeValid_prime [2, 17, 26119] ⟨888047, 5, [(2, 1), (17, 1), (26119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_26119
  · decide +kernel

theorem prime_979543 : Nat.Prime 979543 := by
  apply nodeValid_prime [2, 3, 54419] ⟨979543, 3, [(2, 1), (3, 2), (54419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54419
  · decide +kernel

theorem prime_1045829 : Nat.Prime 1045829 := by
  apply nodeValid_prime [2, 7, 41, 911] ⟨1045829, 2, [(2, 2), (7, 1), (41, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_911
  · decide +kernel

theorem prime_1113181 : Nat.Prime 1113181 := by
  apply nodeValid_prime [2, 3, 5, 18553] ⟨1113181, 2, [(2, 2), (3, 1), (5, 1), (18553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18553
  · decide +kernel

theorem prime_1592197 : Nat.Prime 1592197 := by
  apply nodeValid_prime [2, 3, 277, 479] ⟨1592197, 2, [(2, 2), (3, 1), (277, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_479
  · decide +kernel

theorem prime_1609901 : Nat.Prime 1609901 := by
  apply nodeValid_prime [2, 5, 17, 947] ⟨1609901, 2, [(2, 2), (5, 2), (17, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_947
  · decide +kernel

theorem prime_1688573 : Nat.Prime 1688573 := by
  apply nodeValid_prime [2, 139, 3037] ⟨1688573, 2, [(2, 2), (139, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_3037
  · decide +kernel

theorem prime_1711669 : Nat.Prime 1711669 := by
  apply nodeValid_prime [2, 3, 7, 41, 71] ⟨1711669, 6, [(2, 2), (3, 1), (7, 2), (41, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_71
  · decide +kernel

theorem prime_1857509 : Nat.Prime 1857509 := by
  apply nodeValid_prime [2, 29, 67, 239] ⟨1857509, 2, [(2, 2), (29, 1), (67, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_67
    · exact prime_239
  · decide +kernel

theorem prime_2091659 : Nat.Prime 2091659 := by
  apply nodeValid_prime [2, 1045829] ⟨2091659, 2, [(2, 1), (1045829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1045829
  · decide +kernel

theorem prime_2203303 : Nat.Prime 2203303 := by
  apply nodeValid_prime [2, 3, 17, 21601] ⟨2203303, 5, [(2, 1), (3, 1), (17, 1), (21601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_21601
  · decide +kernel

theorem prime_2210413 : Nat.Prime 2210413 := by
  apply nodeValid_prime [2, 3, 167, 1103] ⟨2210413, 2, [(2, 2), (3, 1), (167, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_1103
  · decide +kernel

theorem prime_2295053 : Nat.Prime 2295053 := by
  apply nodeValid_prime [2, 573763] ⟨2295053, 2, [(2, 2), (573763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_573763
  · decide +kernel

theorem prime_2410351 : Nat.Prime 2410351 := by
  apply nodeValid_prime [2, 3, 5, 16069] ⟨2410351, 3, [(2, 1), (3, 1), (5, 2), (16069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16069
  · decide +kernel

theorem prime_2653621 : Nat.Prime 2653621 := by
  apply nodeValid_prime [2, 3, 5, 47, 941] ⟨2653621, 7, [(2, 2), (3, 1), (5, 1), (47, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_941
  · decide +kernel

theorem prime_3040357 : Nat.Prime 3040357 := by
  apply nodeValid_prime [2, 3, 11, 31, 743] ⟨3040357, 2, [(2, 2), (3, 1), (11, 1), (31, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_743
  · decide +kernel

theorem prime_3272651 : Nat.Prime 3272651 := by
  apply nodeValid_prime [2, 5, 29, 37, 61] ⟨3272651, 2, [(2, 1), (5, 2), (29, 1), (37, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_37
    · exact prime_61
  · decide +kernel

theorem prime_3691273 : Nat.Prime 3691273 := by
  apply nodeValid_prime [2, 3, 13, 11831] ⟨3691273, 7, [(2, 3), (3, 1), (13, 1), (11831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_11831
  · decide +kernel

theorem prime_3744187 : Nat.Prime 3744187 := by
  apply nodeValid_prime [2, 3, 624031] ⟨3744187, 3, [(2, 1), (3, 1), (624031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_624031
  · decide +kernel

theorem prime_4120163 : Nat.Prime 4120163 := by
  apply nodeValid_prime [2, 337, 6113] ⟨4120163, 2, [(2, 1), (337, 1), (6113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_6113
  · decide +kernel

theorem prime_4561399 : Nat.Prime 4561399 := by
  apply nodeValid_prime [2, 3, 211, 1201] ⟨4561399, 3, [(2, 1), (3, 2), (211, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_1201
  · decide +kernel

theorem prime_4641191 : Nat.Prime 4641191 := by
  apply nodeValid_prime [2, 5, 464119] ⟨4641191, 7, [(2, 1), (5, 1), (464119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_464119
  · decide +kernel

theorem prime_4928513 : Nat.Prime 4928513 := by
  apply nodeValid_prime [2, 4813] ⟨4928513, 3, [(2, 10), (4813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4813
  · decide +kernel

theorem prime_6846677 : Nat.Prime 6846677 := by
  apply nodeValid_prime [2, 1711669] ⟨6846677, 2, [(2, 2), (1711669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1711669
  · decide +kernel

theorem prime_7788047 : Nat.Prime 7788047 := by
  apply nodeValid_prime [2, 7, 556289] ⟨7788047, 5, [(2, 1), (7, 1), (556289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_556289
  · decide +kernel

theorem prime_8925439 : Nat.Prime 8925439 := by
  apply nodeValid_prime [2, 3, 1093, 1361] ⟨8925439, 3, [(2, 1), (3, 1), (1093, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1093
    · exact prime_1361
  · decide +kernel

theorem prime_16167713 : Nat.Prime 16167713 := by
  apply nodeValid_prime [2, 11, 23, 1997] ⟨16167713, 3, [(2, 5), (11, 1), (23, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_1997
  · decide +kernel

theorem prime_21920321 : Nat.Prime 21920321 := by
  apply nodeValid_prime [2, 5, 68501] ⟨21920321, 3, [(2, 6), (5, 1), (68501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_68501
  · decide +kernel

theorem prime_23439151 : Nat.Prime 23439151 := by
  apply nodeValid_prime [2, 3, 5, 7, 1063] ⟨23439151, 3, [(2, 1), (3, 2), (5, 2), (7, 2), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1063
  · decide +kernel

theorem prime_39448163 : Nat.Prime 39448163 := by
  apply nodeValid_prime [2, 13, 769, 1973] ⟨39448163, 2, [(2, 1), (13, 1), (769, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_769
    · exact prime_1973
  · decide +kernel

theorem prime_42530023 : Nat.Prime 42530023 := by
  apply nodeValid_prime [2, 3, 17, 15443] ⟨42530023, 5, [(2, 1), (3, 4), (17, 1), (15443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_15443
  · decide +kernel

theorem prime_42731771 : Nat.Prime 42731771 := by
  apply nodeValid_prime [2, 5, 359, 11903] ⟨42731771, 2, [(2, 1), (5, 1), (359, 1), (11903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_359
    · exact prime_11903
  · decide +kernel

theorem prime_52458853 : Nat.Prime 52458853 := by
  apply nodeValid_prime [2, 3, 751, 5821] ⟨52458853, 2, [(2, 2), (3, 1), (751, 1), (5821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_751
    · exact prime_5821
  · decide +kernel

theorem prime_70260577 : Nat.Prime 70260577 := by
  apply nodeValid_prime [2, 3, 731881] ⟨70260577, 5, [(2, 5), (3, 1), (731881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_731881
  · decide +kernel

theorem prime_84253583 : Nat.Prime 84253583 := by
  apply nodeValid_prime [2, 7, 1049, 5737] ⟨84253583, 5, [(2, 1), (7, 1), (1049, 1), (5737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1049
    · exact prime_5737
  · decide +kernel

theorem prime_88669613 : Nat.Prime 88669613 := by
  apply nodeValid_prime [2, 37, 43, 13933] ⟨88669613, 2, [(2, 2), (37, 1), (43, 1), (13933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_43
    · exact prime_13933
  · decide +kernel

theorem prime_100274443 : Nat.Prime 100274443 := by
  apply nodeValid_prime [2, 3, 2683, 6229] ⟨100274443, 3, [(2, 1), (3, 1), (2683, 1), (6229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2683
    · exact prime_6229
  · decide +kernel

theorem prime_104837237 : Nat.Prime 104837237 := by
  apply nodeValid_prime [2, 7, 3744187] ⟨104837237, 2, [(2, 2), (7, 1), (3744187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3744187
  · decide +kernel

theorem prime_112104271 : Nat.Prime 112104271 := by
  apply nodeValid_prime [2, 3, 5, 415201] ⟨112104271, 3, [(2, 1), (3, 3), (5, 1), (415201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_415201
  · decide +kernel

theorem prime_154236559 : Nat.Prime 154236559 := by
  apply nodeValid_prime [2, 3, 7, 29, 126631] ⟨154236559, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (126631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_126631
  · decide +kernel

theorem prime_169217351 : Nat.Prime 169217351 := by
  apply nodeValid_prime [2, 5, 929, 3643] ⟨169217351, 7, [(2, 1), (5, 2), (929, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_929
    · exact prime_3643
  · decide +kernel

theorem prime_175362569 : Nat.Prime 175362569 := by
  apply nodeValid_prime [2, 21920321] ⟨175362569, 3, [(2, 3), (21920321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21920321
  · decide +kernel

theorem prime_191578759 : Nat.Prime 191578759 := by
  apply nodeValid_prime [2, 3, 7, 4561399] ⟨191578759, 7, [(2, 1), (3, 1), (7, 1), (4561399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4561399
  · decide +kernel

theorem prime_216467291 : Nat.Prime 216467291 := by
  apply nodeValid_prime [2, 5, 13, 17, 41, 2389] ⟨216467291, 6, [(2, 1), (5, 1), (13, 1), (17, 1), (41, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_41
    · exact prime_2389
  · decide +kernel

theorem prime_237892043 : Nat.Prime 237892043 := by
  apply nodeValid_prime [2, 8537, 13933] ⟨237892043, 2, [(2, 1), (8537, 1), (13933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8537
    · exact prime_13933
  · decide +kernel

theorem prime_242811913 : Nat.Prime 242811913 := by
  apply nodeValid_prime [2, 3, 7, 227, 6367] ⟨242811913, 5, [(2, 3), (3, 1), (7, 1), (227, 1), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_227
    · exact prime_6367
  · decide +kernel

theorem prime_314753119 : Nat.Prime 314753119 := by
  apply nodeValid_prime [2, 3, 52458853] ⟨314753119, 3, [(2, 1), (3, 1), (52458853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52458853
  · decide +kernel

theorem prime_338434703 : Nat.Prime 338434703 := by
  apply nodeValid_prime [2, 169217351] ⟨338434703, 5, [(2, 1), (169217351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_169217351
  · decide +kernel

theorem prime_346162667 : Nat.Prime 346162667 := by
  apply nodeValid_prime [2, 3301, 52433] ⟨346162667, 2, [(2, 1), (3301, 1), (52433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3301
    · exact prime_52433
  · decide +kernel

theorem prime_446674223 : Nat.Prime 446674223 := by
  apply nodeValid_prime [2, 5323, 41957] ⟨446674223, 5, [(2, 1), (5323, 1), (41957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5323
    · exact prime_41957
  · decide +kernel

theorem prime_547277891 : Nat.Prime 547277891 := by
  apply nodeValid_prime [2, 5, 251, 337, 647] ⟨547277891, 2, [(2, 1), (5, 1), (251, 1), (337, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_251
    · exact prime_337
    · exact prime_647
  · decide +kernel

theorem prime_587337431 : Nat.Prime 587337431 := by
  apply nodeValid_prime [2, 5, 23, 43, 59387] ⟨587337431, 7, [(2, 1), (5, 1), (23, 1), (43, 1), (59387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_43
    · exact prime_59387
  · decide +kernel

theorem prime_789168461 : Nat.Prime 789168461 := by
  apply nodeValid_prime [2, 5, 1723, 22901] ⟨789168461, 2, [(2, 2), (5, 1), (1723, 1), (22901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1723
    · exact prime_22901
  · decide +kernel

theorem prime_983352779 : Nat.Prime 983352779 := by
  apply nodeValid_prime [2, 53, 73, 127081] ⟨983352779, 2, [(2, 1), (53, 1), (73, 1), (127081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_73
    · exact prime_127081
  · decide +kernel

theorem prime_1057906441 : Nat.Prime 1057906441 := by
  apply nodeValid_prime [2, 3, 5, 979543] ⟨1057906441, 13, [(2, 3), (3, 3), (5, 1), (979543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_979543
  · decide +kernel

theorem prime_1139006003 : Nat.Prime 1139006003 := by
  apply nodeValid_prime [2, 37, 1181, 13033] ⟨1139006003, 2, [(2, 1), (37, 1), (1181, 1), (13033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1181
    · exact prime_13033
  · decide +kernel

theorem prime_1298803747 : Nat.Prime 1298803747 := by
  apply nodeValid_prime [2, 3, 216467291] ⟨1298803747, 2, [(2, 1), (3, 1), (216467291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_216467291
  · decide +kernel

theorem prime_1668357133 : Nat.Prime 1668357133 := by
  apply nodeValid_prime [2, 3, 13, 31, 344987] ⟨1668357133, 2, [(2, 2), (3, 1), (13, 1), (31, 1), (344987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_344987
  · decide +kernel

theorem prime_1866455197 : Nat.Prime 1866455197 := by
  apply nodeValid_prime [2, 3, 19, 29, 83, 179] ⟨1866455197, 5, [(2, 2), (3, 1), (19, 2), (29, 1), (83, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_83
    · exact prime_179
  · decide +kernel

theorem prime_7167939197 : Nat.Prime 7167939197 := by
  apply nodeValid_prime [2, 11, 151, 311, 3469] ⟨7167939197, 2, [(2, 2), (11, 1), (151, 1), (311, 1), (3469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_151
    · exact prime_311
    · exact prime_3469
  · decide +kernel

theorem prime_10624944947 : Nat.Prime 10624944947 := by
  apply nodeValid_prime [2, 7, 11, 79, 873331] ⟨10624944947, 5, [(2, 1), (7, 1), (11, 1), (79, 1), (873331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_79
    · exact prime_873331
  · decide +kernel

theorem prime_12580468441 : Nat.Prime 12580468441 := by
  apply nodeValid_prime [2, 3, 5, 104837237] ⟨12580468441, 17, [(2, 3), (3, 1), (5, 1), (104837237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_104837237
  · decide +kernel

theorem prime_37570722757 : Nat.Prime 37570722757 := by
  apply nodeValid_prime [2, 3, 7, 29, 2203303] ⟨37570722757, 5, [(2, 2), (3, 1), (7, 2), (29, 1), (2203303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_2203303
  · decide +kernel

theorem prime_67347236483 : Nat.Prime 67347236483 := by
  apply nodeValid_prime [2, 17, 947, 2091659] ⟨67347236483, 5, [(2, 1), (17, 1), (947, 1), (2091659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_947
    · exact prime_2091659
  · decide +kernel

theorem prime_99435226087 : Nat.Prime 99435226087 := by
  apply nodeValid_prime [2, 3, 7, 789168461] ⟨99435226087, 3, [(2, 1), (3, 2), (7, 1), (789168461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_789168461
  · decide +kernel

theorem prime_143358783941 : Nat.Prime 143358783941 := by
  apply nodeValid_prime [2, 5, 7167939197] ⟨143358783941, 2, [(2, 2), (5, 1), (7167939197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7167939197
  · decide +kernel

theorem prime_222075814607 : Nat.Prime 222075814607 := by
  apply nodeValid_prime [2, 131, 1249, 678637] ⟨222075814607, 5, [(2, 1), (131, 1), (1249, 1), (678637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_1249
    · exact prime_678637
  · decide +kernel

theorem prime_223931919527 : Nat.Prime 223931919527 := by
  apply nodeValid_prime [2, 7, 12539, 182233] ⟨223931919527, 5, [(2, 1), (7, 2), (12539, 1), (182233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12539
    · exact prime_182233
  · decide +kernel

theorem prime_224490791221 : Nat.Prime 224490791221 := by
  apply nodeValid_prime [2, 3, 5, 17, 1613, 136447] ⟨224490791221, 13, [(2, 2), (3, 1), (5, 1), (17, 1), (1613, 1), (136447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1613
    · exact prime_136447
  · decide +kernel

theorem prime_286717567883 : Nat.Prime 286717567883 := by
  apply nodeValid_prime [2, 143358783941] ⟨286717567883, 2, [(2, 1), (143358783941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_143358783941
  · decide +kernel

theorem prime_287434100339 : Nat.Prime 287434100339 := by
  apply nodeValid_prime [2, 7, 11, 1866455197] ⟨287434100339, 2, [(2, 1), (7, 1), (11, 1), (1866455197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1866455197
  · decide +kernel

theorem prime_332004443611 : Nat.Prime 332004443611 := by
  apply nodeValid_prime [2, 3, 5, 7, 29, 7788047] ⟨332004443611, 7, [(2, 1), (3, 1), (5, 1), (7, 2), (29, 1), (7788047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_7788047
  · decide +kernel

theorem prime_335060980061 : Nat.Prime 335060980061 := by
  apply nodeValid_prime [2, 5, 1877, 8925439] ⟨335060980061, 3, [(2, 2), (5, 1), (1877, 1), (8925439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1877
    · exact prime_8925439
  · decide +kernel

theorem prime_401070597199 : Nat.Prime 401070597199 := by
  apply nodeValid_prime [2, 3, 30241, 2210413] ⟨401070597199, 21, [(2, 1), (3, 1), (30241, 1), (2210413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30241
    · exact prime_2210413
  · decide +kernel

theorem prime_404083418899 : Nat.Prime 404083418899 := by
  apply nodeValid_prime [2, 3, 67347236483] ⟨404083418899, 2, [(2, 1), (3, 1), (67347236483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67347236483
  · decide +kernel

theorem prime_669007658177 : Nat.Prime 669007658177 := by
  apply nodeValid_prime [2, 11, 13, 43, 67, 25373] ⟨669007658177, 3, [(2, 6), (11, 1), (13, 1), (43, 1), (67, 1), (25373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_43
    · exact prime_67
    · exact prime_25373
  · decide +kernel

theorem prime_1006019362603 : Nat.Prime 1006019362603 := by
  apply nodeValid_prime [2, 3, 99667, 560767] ⟨1006019362603, 2, [(2, 1), (3, 2), (99667, 1), (560767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_99667
    · exact prime_560767
  · decide +kernel

theorem prime_1007693625007 : Nat.Prime 1007693625007 := by
  apply nodeValid_prime [2, 3, 37, 307, 4928513] ⟨1007693625007, 3, [(2, 1), (3, 2), (37, 1), (307, 1), (4928513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_307
    · exact prime_4928513
  · decide +kernel

theorem prime_3977408962477 : Nat.Prime 3977408962477 := by
  apply nodeValid_prime [2, 3, 97, 1139006003] ⟨3977408962477, 2, [(2, 2), (3, 2), (97, 1), (1139006003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1139006003
  · decide +kernel

theorem prime_3977409043481 : Nat.Prime 3977409043481 := by
  apply nodeValid_prime [2, 5, 99435226087] ⟨3977409043481, 3, [(2, 3), (5, 1), (99435226087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_99435226087
  · decide +kernel

theorem prime_3977409043831 : Nat.Prime 3977409043831 := by
  apply nodeValid_prime [2, 3, 5, 383, 346162667] ⟨3977409043831, 6, [(2, 1), (3, 1), (5, 1), (383, 1), (346162667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
    · exact prime_346162667
  · decide +kernel

theorem prime_3980730207403 : Nat.Prime 3980730207403 := by
  apply nodeValid_prime [2, 3, 13, 20981, 270271] ⟨3980730207403, 2, [(2, 1), (3, 3), (13, 1), (20981, 1), (270271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_20981
    · exact prime_270271
  · decide +kernel

theorem prime_3980730316291 : Nat.Prime 3980730316291 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 19, 733, 14957] ⟨3980730316291, 3, [(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (19, 1), (733, 1), (14957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_733
    · exact prime_14957
  · decide +kernel

theorem prime_3980730316301 : Nat.Prime 3980730316301 := by
  apply nodeValid_prime [2, 5, 227, 175362569] ⟨3980730316301, 2, [(2, 2), (5, 2), (227, 1), (175362569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
    · exact prime_175362569
  · decide +kernel

theorem prime_3984053323333 : Nat.Prime 3984053323333 := by
  apply nodeValid_prime [2, 3, 332004443611] ⟨3984053323333, 6, [(2, 2), (3, 1), (332004443611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_332004443611
  · decide +kernel

theorem prime_3984053323717 : Nat.Prime 3984053323717 := by
  apply nodeValid_prime [2, 3, 109, 338434703] ⟨3984053323717, 2, [(2, 2), (3, 3), (109, 1), (338434703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_338434703
  · decide +kernel

theorem prime_3984053329079 : Nat.Prime 3984053329079 := by
  apply nodeValid_prime [2, 157, 3877, 3272651] ⟨3984053329079, 13, [(2, 1), (157, 1), (3877, 1), (3272651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_3877
    · exact prime_3272651
  · decide +kernel

theorem prime_3987378327979 : Nat.Prime 3987378327979 := by
  apply nodeValid_prime [2, 3, 19, 167, 269, 28837] ⟨3987378327979, 2, [(2, 1), (3, 4), (19, 1), (167, 1), (269, 1), (28837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_167
    · exact prime_269
    · exact prime_28837
  · decide +kernel

theorem prime_3987378386339 : Nat.Prime 3987378386339 := by
  apply nodeValid_prime [2, 317, 389, 16167713] ⟨3987378386339, 2, [(2, 1), (317, 1), (389, 1), (16167713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_389
    · exact prime_16167713
  · decide +kernel

theorem prime_3987378386837 : Nat.Prime 3987378386837 := by
  apply nodeValid_prime [2, 13, 37, 503, 4120163] ⟨3987378386837, 2, [(2, 2), (13, 1), (37, 1), (503, 1), (4120163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_503
    · exact prime_4120163
  · decide +kernel

theorem prime_3990704904607 : Nat.Prime 3990704904607 := by
  apply nodeValid_prime [2, 3, 7, 41, 3257, 711539] ⟨3990704904607, 5, [(2, 1), (3, 1), (7, 1), (41, 1), (3257, 1), (711539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_3257
    · exact prime_711539
  · decide +kernel

theorem prime_3990704905037 : Nat.Prime 3990704905037 := by
  apply nodeValid_prime [2, 127, 7057, 1113181] ⟨3990704905037, 2, [(2, 2), (127, 1), (7057, 1), (1113181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_7057
    · exact prime_1113181
  · decide +kernel

theorem prime_3990705208933 : Nat.Prime 3990705208933 := by
  apply nodeValid_prime [2, 3, 13, 179, 6653, 21481] ⟨3990705208933, 2, [(2, 2), (3, 1), (13, 1), (179, 1), (6653, 1), (21481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_179
    · exact prime_6653
    · exact prime_21481
  · decide +kernel

theorem prime_3994033967633 : Nat.Prime 3994033967633 := by
  apply nodeValid_prime [2, 1303, 191578759] ⟨3994033967633, 3, [(2, 4), (1303, 1), (191578759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1303
    · exact prime_191578759
  · decide +kernel

theorem prime_3994034047973 : Nat.Prime 3994034047973 := by
  apply nodeValid_prime [2, 11261, 88669613] ⟨3994034047973, 2, [(2, 2), (11261, 1), (88669613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11261
    · exact prime_88669613
  · decide +kernel

theorem prime_3994034048519 : Nat.Prime 3994034048519 := by
  apply nodeValid_prime [2, 41, 89, 547277891] ⟨3994034048519, 7, [(2, 1), (41, 1), (89, 1), (547277891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_89
    · exact prime_547277891
  · decide +kernel

theorem prime_3997364611301 : Nat.Prime 3997364611301 := by
  apply nodeValid_prime [2, 5, 127, 314753119] ⟨3997364611301, 3, [(2, 2), (5, 2), (127, 1), (314753119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_127
    · exact prime_314753119
  · decide +kernel

theorem prime_3997364662927 : Nat.Prime 3997364662927 := by
  apply nodeValid_prime [2, 3, 222075814607] ⟨3997364662927, 3, [(2, 1), (3, 2), (222075814607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_222075814607
  · decide +kernel

theorem prime_3997364664017 : Nat.Prime 3997364664017 := by
  apply nodeValid_prime [2, 103651, 2410351] ⟨3997364664017, 3, [(2, 4), (103651, 1), (2410351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103651
    · exact prime_2410351
  · decide +kernel

theorem prime_4000697135173 : Nat.Prime 4000697135173 := by
  apply nodeValid_prime [2, 3, 1319, 84253583] ⟨4000697135173, 2, [(2, 2), (3, 2), (1319, 1), (84253583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1319
    · exact prime_84253583
  · decide +kernel

theorem prime_4000697359259 : Nat.Prime 4000697359259 := by
  apply nodeValid_prime [2, 23, 89, 607, 1609901] ⟨4000697359259, 6, [(2, 1), (23, 1), (89, 1), (607, 1), (1609901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_89
    · exact prime_607
    · exact prime_1609901
  · decide +kernel

theorem prime_4000697359619 : Nat.Prime 4000697359619 := by
  apply nodeValid_prime [2, 430999, 4641191] ⟨4000697359619, 2, [(2, 1), (430999, 1), (4641191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_430999
    · exact prime_4641191
  · decide +kernel

theorem prime_4004031540329 : Nat.Prime 4004031540329 := by
  apply nodeValid_prime [2, 227, 1187, 1857509] ⟨4004031540329, 3, [(2, 3), (227, 1), (1187, 1), (1857509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_1187
    · exact prime_1857509
  · decide +kernel

theorem prime_4004031540449 : Nat.Prime 4004031540449 := by
  apply nodeValid_prime [2, 89, 883, 1592197] ⟨4004031540449, 3, [(2, 5), (89, 1), (883, 1), (1592197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_883
    · exact prime_1592197
  · decide +kernel

theorem prime_4004031545359 : Nat.Prime 4004031545359 := by
  apply nodeValid_prime [2, 3, 13, 17, 71, 42530023] ⟨4004031545359, 3, [(2, 1), (3, 1), (13, 1), (17, 1), (71, 1), (42530023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_71
    · exact prime_42530023
  · decide +kernel

theorem prime_4007367812153 : Nat.Prime 4007367812153 := by
  apply nodeValid_prime [2, 2063, 242811913] ⟨4007367812153, 3, [(2, 3), (2063, 1), (242811913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2063
    · exact prime_242811913
  · decide +kernel

theorem prime_4007367812411 : Nat.Prime 4007367812411 := by
  apply nodeValid_prime [2, 5, 19, 107, 4363, 45179] ⟨4007367812411, 2, [(2, 1), (5, 1), (19, 1), (107, 1), (4363, 1), (45179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_107
    · exact prime_4363
    · exact prime_45179
  · decide +kernel

theorem prime_4007367840053 : Nat.Prime 4007367840053 := by
  apply nodeValid_prime [2, 97, 103, 100274443] ⟨4007367840053, 2, [(2, 2), (97, 1), (103, 1), (100274443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_103
    · exact prime_100274443
  · decide +kernel

theorem prime_4010705970737 : Nat.Prime 4010705970737 := by
  apply nodeValid_prime [2, 193, 1298803747] ⟨4010705970737, 3, [(2, 4), (193, 1), (1298803747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_1298803747
  · decide +kernel

theorem prime_4010705971991 : Nat.Prime 4010705971991 := by
  apply nodeValid_prime [2, 5, 401070597199] ⟨4010705971991, 17, [(2, 1), (5, 1), (401070597199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_401070597199
  · decide +kernel

theorem prime_4010706005723 : Nat.Prime 4010706005723 := by
  apply nodeValid_prime [2, 13, 71, 14557, 149251] ⟨4010706005723, 2, [(2, 1), (13, 1), (71, 1), (14557, 1), (149251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71
    · exact prime_14557
    · exact prime_149251
  · decide +kernel

theorem prime_4014045949063 : Nat.Prime 4014045949063 := by
  apply nodeValid_prime [2, 3, 669007658177] ⟨4014045949063, 3, [(2, 1), (3, 1), (669007658177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_669007658177
  · decide +kernel

theorem prime_4014045950363 : Nat.Prime 4014045950363 := by
  apply nodeValid_prime [2, 7, 286717567883] ⟨4014045950363, 5, [(2, 1), (7, 1), (286717567883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_286717567883
  · decide +kernel

theorem prime_4014046043879 : Nat.Prime 4014046043879 := by
  apply nodeValid_prime [2, 13, 157, 983352779] ⟨4014046043879, 14, [(2, 1), (13, 1), (157, 1), (983352779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_157
    · exact prime_983352779
  · decide +kernel

theorem prime_4017387961663 : Nat.Prime 4017387961663 := by
  apply nodeValid_prime [2, 3, 1499, 446674223] ⟨4017387961663, 3, [(2, 1), (3, 1), (1499, 1), (446674223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1499
    · exact prime_446674223
  · decide +kernel

theorem prime_4017388028041 : Nat.Prime 4017388028041 := by
  apply nodeValid_prime [2, 3, 5, 19, 587337431] ⟨4017388028041, 13, [(2, 3), (3, 2), (5, 1), (19, 1), (587337431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_587337431
  · decide +kernel

theorem prime_4017388029007 : Nat.Prime 4017388029007 := by
  apply nodeValid_prime [2, 3, 11, 31, 37, 71, 293, 2551] ⟨4017388029007, 3, [(2, 1), (3, 1), (11, 1), (31, 1), (37, 1), (71, 1), (293, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_37
    · exact prime_71
    · exact prime_293
    · exact prime_2551
  · decide +kernel

theorem prime_4020731760733 : Nat.Prime 4020731760733 := by
  apply nodeValid_prime [2, 3, 335060980061] ⟨4020731760733, 2, [(2, 2), (3, 1), (335060980061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_335060980061
  · decide +kernel

theorem prime_4020731779403 : Nat.Prime 4020731779403 := by
  apply nodeValid_prime [2, 13, 31, 71, 70260577] ⟨4020731779403, 2, [(2, 1), (13, 1), (31, 1), (71, 1), (70260577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_71
    · exact prime_70260577
  · decide +kernel

theorem prime_4020731783687 : Nat.Prime 4020731783687 := by
  apply nodeValid_prime [2, 79, 227, 112104271] ⟨4020731783687, 5, [(2, 1), (79, 1), (227, 1), (112104271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_227
    · exact prime_112104271
  · decide +kernel

theorem prime_4024077404747 : Nat.Prime 4024077404747 := by
  apply nodeValid_prime [2, 7, 287434100339] ⟨4024077404747, 2, [(2, 1), (7, 1), (287434100339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_287434100339
  · decide +kernel

theorem prime_4024077404797 : Nat.Prime 4024077404797 := by
  apply nodeValid_prime [2, 3, 67, 1668357133] ⟨4024077404797, 5, [(2, 2), (3, 2), (67, 1), (1668357133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1668357133
  · decide +kernel

theorem prime_4024077450413 : Nat.Prime 4024077450413 := by
  apply nodeValid_prime [2, 1006019362603] ⟨4024077450413, 2, [(2, 2), (1006019362603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1006019362603
  · decide +kernel

theorem prime_4027425028609 : Nat.Prime 4027425028609 := by
  apply nodeValid_prime [2, 3, 17, 154236559] ⟨4027425028609, 37, [(2, 9), (3, 1), (17, 1), (154236559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_154236559
  · decide +kernel

theorem prime_4027425067403 : Nat.Prime 4027425067403 := by
  apply nodeValid_prime [2, 11, 17, 37, 1223, 237973] ⟨4027425067403, 2, [(2, 1), (11, 1), (17, 1), (37, 1), (1223, 1), (237973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_37
    · exact prime_1223
    · exact prime_237973
  · decide +kernel

theorem prime_4027425068237 : Nat.Prime 4027425068237 := by
  apply nodeValid_prime [2, 2237, 7333, 61379] ⟨4027425068237, 2, [(2, 2), (2237, 1), (7333, 1), (61379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2237
    · exact prime_7333
    · exact prime_61379
  · decide +kernel

theorem prime_4030774500029 : Nat.Prime 4030774500029 := by
  apply nodeValid_prime [2, 1007693625007] ⟨4030774500029, 2, [(2, 2), (1007693625007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1007693625007
  · decide +kernel

theorem prime_4030774549861 : Nat.Prime 4030774549861 := by
  apply nodeValid_prime [2, 3, 5, 19, 43, 163, 504461] ⟨4030774549861, 10, [(2, 2), (3, 1), (5, 1), (19, 1), (43, 1), (163, 1), (504461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_43
    · exact prime_163
    · exact prime_504461
  · decide +kernel

theorem prime_4030774551487 : Nat.Prime 4030774551487 := by
  apply nodeValid_prime [2, 3, 223931919527] ⟨4030774551487, 6, [(2, 1), (3, 2), (223931919527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223931919527
  · decide +kernel

theorem prime_4034125818787 : Nat.Prime 4034125818787 := by
  apply nodeValid_prime [2, 3, 7, 26021, 3691273] ⟨4034125818787, 2, [(2, 1), (3, 1), (7, 1), (26021, 1), (3691273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_26021
    · exact prime_3691273
  · decide +kernel

theorem prime_4034125819001 : Nat.Prime 4034125819001 := by
  apply nodeValid_prime [2, 5, 509, 1051, 7541] ⟨4034125819001, 6, [(2, 3), (5, 3), (509, 1), (1051, 1), (7541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_509
    · exact prime_1051
    · exact prime_7541
  · decide +kernel

theorem prime_4034125851403 : Nat.Prime 4034125851403 := by
  apply nodeValid_prime [2, 3, 307, 1297, 1688573] ⟨4034125851403, 2, [(2, 1), (3, 1), (307, 1), (1297, 1), (1688573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_1297
    · exact prime_1688573
  · decide +kernel

theorem prime_4037479044091 : Nat.Prime 4037479044091 := by
  apply nodeValid_prime [2, 3, 5, 151549, 888047] ⟨4037479044091, 2, [(2, 1), (3, 1), (5, 1), (151549, 1), (888047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151549
    · exact prime_888047
  · decide +kernel

theorem prime_4037479044259 : Nat.Prime 4037479044259 := by
  apply nodeValid_prime [2, 3, 11, 23053, 2653621] ⟨4037479044259, 2, [(2, 1), (3, 1), (11, 1), (23053, 1), (2653621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23053
    · exact prime_2653621
  · decide +kernel

theorem prime_4037479079861 : Nat.Prime 4037479079861 := by
  apply nodeValid_prime [2, 5, 19, 10624944947] ⟨4037479079861, 2, [(2, 2), (5, 1), (19, 1), (10624944947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_10624944947
  · decide +kernel

theorem prime_4040834188991 : Nat.Prime 4040834188991 := by
  apply nodeValid_prime [2, 5, 404083418899] ⟨4040834188991, 13, [(2, 1), (5, 1), (404083418899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_404083418899
  · decide +kernel

theorem prime_4040834241979 : Nat.Prime 4040834241979 := by
  apply nodeValid_prime [2, 3, 224490791221] ⟨4040834241979, 10, [(2, 1), (3, 2), (224490791221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_224490791221
  · decide +kernel

theorem prime_4040834242399 : Nat.Prime 4040834242399 := by
  apply nodeValid_prime [2, 3, 19, 149, 237892043] ⟨4040834242399, 6, [(2, 1), (3, 1), (19, 1), (149, 1), (237892043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_149
    · exact prime_237892043
  · decide +kernel

theorem prime_4044191113541 : Nat.Prime 4044191113541 := by
  apply nodeValid_prime [2, 5, 8627, 23439151] ⟨4044191113541, 2, [(2, 2), (5, 1), (8627, 1), (23439151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8627
    · exact prime_23439151
  · decide +kernel

theorem prime_4044191113559 : Nat.Prime 4044191113559 := by
  apply nodeValid_prime [2, 173, 14423, 810401] ⟨4044191113559, 7, [(2, 1), (173, 1), (14423, 1), (810401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_14423
    · exact prime_810401
  · decide +kernel

theorem prime_4044191183891 : Nat.Prime 4044191183891 := by
  apply nodeValid_prime [2, 5, 11, 13, 29, 127, 767881] ⟨4044191183891, 2, [(2, 1), (5, 1), (11, 1), (13, 1), (29, 1), (127, 1), (767881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_29
    · exact prime_127
    · exact prime_767881
  · decide +kernel

theorem prime_4047550042091 : Nat.Prime 4047550042091 := by
  apply nodeValid_prime [2, 5, 31, 1907, 6846677] ⟨4047550042091, 2, [(2, 1), (5, 1), (31, 1), (1907, 1), (6846677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1907
    · exact prime_6846677
  · decide +kernel

theorem prime_4047550043267 : Nat.Prime 4047550043267 := by
  apply nodeValid_prime [2, 1913, 1057906441] ⟨4047550043267, 2, [(2, 1), (1913, 1), (1057906441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1913
    · exact prime_1057906441
  · decide +kernel

theorem prime_4047550065101 : Nat.Prime 4047550065101 := by
  apply nodeValid_prime [2, 5, 17, 29, 2347, 34981] ⟨4047550065101, 2, [(2, 2), (5, 2), (17, 1), (29, 1), (2347, 1), (34981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_29
    · exact prime_2347
    · exact prime_34981
  · decide +kernel

theorem prime_4050910837903 : Nat.Prime 4050910837903 := by
  apply nodeValid_prime [2, 3, 739, 9497, 96199] ⟨4050910837903, 3, [(2, 1), (3, 1), (739, 1), (9497, 1), (96199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_739
    · exact prime_9497
    · exact prime_96199
  · decide +kernel

theorem prime_4050910838003 : Nat.Prime 4050910838003 := by
  apply nodeValid_prime [2, 7, 23, 12580468441] ⟨4050910838003, 2, [(2, 1), (7, 1), (23, 1), (12580468441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_12580468441
  · decide +kernel

theorem prime_4050910838287 : Nat.Prime 4050910838287 := by
  apply nodeValid_prime [2, 3, 13, 19, 397, 2295053] ⟨4050910838287, 11, [(2, 1), (3, 2), (13, 1), (19, 1), (397, 1), (2295053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_397
    · exact prime_2295053
  · decide +kernel

theorem prime_4054273494503 : Nat.Prime 4054273494503 := by
  apply nodeValid_prime [2, 7, 11, 1237, 3040357] ⟨4054273494503, 5, [(2, 1), (7, 2), (11, 1), (1237, 1), (3040357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1237
    · exact prime_3040357
  · decide +kernel

theorem prime_4054273495273 : Nat.Prime 4054273495273 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 23, 557, 4391] ⟨4054273495273, 15, [(2, 3), (3, 2), (7, 1), (11, 1), (13, 1), (23, 1), (557, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_557
    · exact prime_4391
  · decide +kernel

theorem prime_4054273503209 : Nat.Prime 4054273503209 := by
  apply nodeValid_prime [2, 67, 709, 1117, 9551] ⟨4054273503209, 3, [(2, 3), (67, 1), (709, 1), (1117, 1), (9551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_709
    · exact prime_1117
    · exact prime_9551
  · decide +kernel

theorem prime_4057638046181 : Nat.Prime 4057638046181 := by
  apply nodeValid_prime [2, 5, 37, 139, 39448163] ⟨4057638046181, 2, [(2, 2), (5, 1), (37, 1), (139, 1), (39448163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_139
    · exact prime_39448163
  · decide +kernel

theorem prime_4057638047077 : Nat.Prime 4057638047077 := by
  apply nodeValid_prime [2, 3, 41, 193, 42731771] ⟨4057638047077, 2, [(2, 2), (3, 1), (41, 1), (193, 1), (42731771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_193
    · exact prime_42731771
  · decide +kernel

theorem prime_4057638057757 : Nat.Prime 4057638057757 := by
  apply nodeValid_prime [2, 3, 37570722757] ⟨4057638057757, 2, [(2, 2), (3, 3), (37570722757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37570722757
  · decide +kernel

end Sude.Lucas.Generated
