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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0081

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_12007 : Nat.Prime 12007 := by
  apply nodeValid_prime [2, 3, 23, 29] ⟨12007, 13, [(2, 1), (3, 2), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_17627 : Nat.Prime 17627 := by
  apply nodeValid_prime [2, 7, 1259] ⟨17627, 2, [(2, 1), (7, 1), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1259
  · decide +kernel

theorem prime_20693 : Nat.Prime 20693 := by
  apply nodeValid_prime [2, 7, 739] ⟨20693, 2, [(2, 2), (7, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_739
  · decide +kernel

theorem prime_26849 : Nat.Prime 26849 := by
  apply nodeValid_prime [2, 839] ⟨26849, 3, [(2, 5), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_839
  · decide +kernel

theorem prime_31769 : Nat.Prime 31769 := by
  apply nodeValid_prime [2, 11, 19] ⟨31769, 6, [(2, 3), (11, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_32579 : Nat.Prime 32579 := by
  apply nodeValid_prime [2, 7, 13, 179] ⟨32579, 6, [(2, 1), (7, 1), (13, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_179
  · decide +kernel

theorem prime_36529 : Nat.Prime 36529 := by
  apply nodeValid_prime [2, 3, 761] ⟨36529, 7, [(2, 4), (3, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_761
  · decide +kernel

theorem prime_43261 : Nat.Prime 43261 := by
  apply nodeValid_prime [2, 3, 5, 7, 103] ⟨43261, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_49297 : Nat.Prime 49297 := by
  apply nodeValid_prime [2, 3, 13, 79] ⟨49297, 5, [(2, 4), (3, 1), (13, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_79
  · decide +kernel

theorem prime_53201 : Nat.Prime 53201 := by
  apply nodeValid_prime [2, 5, 7, 19] ⟨53201, 3, [(2, 4), (5, 2), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_57649 : Nat.Prime 57649 := by
  apply nodeValid_prime [2, 3, 1201] ⟨57649, 13, [(2, 4), (3, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1201
  · decide +kernel

theorem prime_58049 : Nat.Prime 58049 := by
  apply nodeValid_prime [2, 907] ⟨58049, 3, [(2, 6), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_907
  · decide +kernel

theorem prime_63853 : Nat.Prime 63853 := by
  apply nodeValid_prime [2, 3, 17, 313] ⟨63853, 2, [(2, 2), (3, 1), (17, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_313
  · decide +kernel

theorem prime_68087 : Nat.Prime 68087 := by
  apply nodeValid_prime [2, 59, 577] ⟨68087, 5, [(2, 1), (59, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_577
  · decide +kernel

theorem prime_71741 : Nat.Prime 71741 := by
  apply nodeValid_prime [2, 5, 17, 211] ⟨71741, 2, [(2, 2), (5, 1), (17, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_211
  · decide +kernel

theorem prime_79997 : Nat.Prime 79997 := by
  apply nodeValid_prime [2, 7, 2857] ⟨79997, 2, [(2, 2), (7, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2857
  · decide +kernel

theorem prime_100403 : Nat.Prime 100403 := by
  apply nodeValid_prime [2, 17, 2953] ⟨100403, 2, [(2, 1), (17, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2953
  · decide +kernel

theorem prime_101837 : Nat.Prime 101837 := by
  apply nodeValid_prime [2, 7, 3637] ⟨101837, 5, [(2, 2), (7, 1), (3637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3637
  · decide +kernel

theorem prime_116099 : Nat.Prime 116099 := by
  apply nodeValid_prime [2, 58049] ⟨116099, 2, [(2, 1), (58049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58049
  · decide +kernel

theorem prime_127481 : Nat.Prime 127481 := by
  apply nodeValid_prime [2, 5, 3187] ⟨127481, 3, [(2, 3), (5, 1), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3187
  · decide +kernel

theorem prime_132241 : Nat.Prime 132241 := by
  apply nodeValid_prime [2, 3, 5, 19, 29] ⟨132241, 11, [(2, 4), (3, 1), (5, 1), (19, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_146117 : Nat.Prime 146117 := by
  apply nodeValid_prime [2, 36529] ⟨146117, 2, [(2, 2), (36529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36529
  · decide +kernel

theorem prime_146359 : Nat.Prime 146359 := by
  apply nodeValid_prime [2, 3, 47, 173] ⟨146359, 3, [(2, 1), (3, 2), (47, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_173
  · decide +kernel

theorem prime_160591 : Nat.Prime 160591 := by
  apply nodeValid_prime [2, 3, 5, 53, 101] ⟨160591, 7, [(2, 1), (3, 1), (5, 1), (53, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_101
  · decide +kernel

theorem prime_174221 : Nat.Prime 174221 := by
  apply nodeValid_prime [2, 5, 31, 281] ⟨174221, 2, [(2, 2), (5, 1), (31, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_281
  · decide +kernel

theorem prime_204067 : Nat.Prime 204067 := by
  apply nodeValid_prime [2, 3, 3779] ⟨204067, 2, [(2, 1), (3, 3), (3779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3779
  · decide +kernel

theorem prime_221489 : Nat.Prime 221489 := by
  apply nodeValid_prime [2, 109, 127] ⟨221489, 3, [(2, 4), (109, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_127
  · decide +kernel

theorem prime_242603 : Nat.Prime 242603 := by
  apply nodeValid_prime [2, 101, 1201] ⟨242603, 2, [(2, 1), (101, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_1201
  · decide +kernel

theorem prime_254963 : Nat.Prime 254963 := by
  apply nodeValid_prime [2, 127481] ⟨254963, 2, [(2, 1), (127481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_127481
  · decide +kernel

theorem prime_287437 : Nat.Prime 287437 := by
  apply nodeValid_prime [2, 3, 17, 1409] ⟨287437, 2, [(2, 2), (3, 1), (17, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1409
  · decide +kernel

theorem prime_297757 : Nat.Prime 297757 := by
  apply nodeValid_prime [2, 3, 919] ⟨297757, 2, [(2, 2), (3, 4), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_919
  · decide +kernel

theorem prime_320767 : Nat.Prime 320767 := by
  apply nodeValid_prime [2, 3, 193, 277] ⟨320767, 3, [(2, 1), (3, 1), (193, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_277
  · decide +kernel

theorem prime_425609 : Nat.Prime 425609 := by
  apply nodeValid_prime [2, 53201] ⟨425609, 3, [(2, 3), (53201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53201
  · decide +kernel

theorem prime_442979 : Nat.Prime 442979 := by
  apply nodeValid_prime [2, 221489] ⟨442979, 2, [(2, 1), (221489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_221489
  · decide +kernel

theorem prime_449173 : Nat.Prime 449173 := by
  apply nodeValid_prime [2, 3, 4159] ⟨449173, 2, [(2, 2), (3, 3), (4159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4159
  · decide +kernel

theorem prime_450367 : Nat.Prime 450367 := by
  apply nodeValid_prime [2, 3, 7, 10723] ⟨450367, 3, [(2, 1), (3, 1), (7, 1), (10723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10723
  · decide +kernel

theorem prime_460463 : Nat.Prime 460463 := by
  apply nodeValid_prime [2, 17, 29, 467] ⟨460463, 5, [(2, 1), (17, 1), (29, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_467
  · decide +kernel

theorem prime_573929 : Nat.Prime 573929 := by
  apply nodeValid_prime [2, 71741] ⟨573929, 3, [(2, 3), (71741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71741
  · decide +kernel

theorem prime_585437 : Nat.Prime 585437 := by
  apply nodeValid_prime [2, 146359] ⟨585437, 2, [(2, 2), (146359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_146359
  · decide +kernel

theorem prime_644377 : Nat.Prime 644377 := by
  apply nodeValid_prime [2, 3, 26849] ⟨644377, 5, [(2, 3), (3, 1), (26849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26849
  · decide +kernel

theorem prime_765283 : Nat.Prime 765283 := by
  apply nodeValid_prime [2, 3, 7, 19, 137] ⟨765283, 5, [(2, 1), (3, 1), (7, 2), (19, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_885959 : Nat.Prime 885959 := by
  apply nodeValid_prime [2, 442979] ⟨885959, 7, [(2, 1), (442979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_442979
  · decide +kernel

theorem prime_915139 : Nat.Prime 915139 := by
  apply nodeValid_prime [2, 3, 7, 269] ⟨915139, 2, [(2, 1), (3, 5), (7, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_269
  · decide +kernel

theorem prime_1141061 : Nat.Prime 1141061 := by
  apply nodeValid_prime [2, 5, 59, 967] ⟨1141061, 3, [(2, 2), (5, 1), (59, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_967
  · decide +kernel

theorem prime_1148621 : Nat.Prime 1148621 := by
  apply nodeValid_prime [2, 5, 11, 23, 227] ⟨1148621, 2, [(2, 2), (5, 1), (11, 1), (23, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_227
  · decide +kernel

theorem prime_1241771 : Nat.Prime 1241771 := by
  apply nodeValid_prime [2, 5, 23, 5399] ⟨1241771, 2, [(2, 1), (5, 1), (23, 1), (5399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_5399
  · decide +kernel

theorem prime_1268279 : Nat.Prime 1268279 := by
  apply nodeValid_prime [2, 11, 57649] ⟨1268279, 11, [(2, 1), (11, 1), (57649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_57649
  · decide +kernel

theorem prime_1361741 : Nat.Prime 1361741 := by
  apply nodeValid_prime [2, 5, 68087] ⟨1361741, 2, [(2, 2), (5, 1), (68087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_68087
  · decide +kernel

theorem prime_1439947 : Nat.Prime 1439947 := by
  apply nodeValid_prime [2, 3, 79997] ⟨1439947, 5, [(2, 1), (3, 2), (79997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79997
  · decide +kernel

theorem prime_1484827 : Nat.Prime 1484827 := by
  apply nodeValid_prime [2, 3, 7, 35353] ⟨1484827, 2, [(2, 1), (3, 1), (7, 1), (35353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_35353
  · decide +kernel

theorem prime_1583851 : Nat.Prime 1583851 := by
  apply nodeValid_prime [2, 3, 5, 10559] ⟨1583851, 11, [(2, 1), (3, 1), (5, 2), (10559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10559
  · decide +kernel

theorem prime_2270441 : Nat.Prime 2270441 := by
  apply nodeValid_prime [2, 5, 31, 1831] ⟨2270441, 3, [(2, 3), (5, 1), (31, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1831
  · decide +kernel

theorem prime_2483543 : Nat.Prime 2483543 := by
  apply nodeValid_prime [2, 1241771] ⟨2483543, 5, [(2, 1), (1241771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1241771
  · decide +kernel

theorem prime_3334531 : Nat.Prime 3334531 := by
  apply nodeValid_prime [2, 3, 5, 41, 2711] ⟨3334531, 7, [(2, 1), (3, 1), (5, 1), (41, 1), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_2711
  · decide +kernel

theorem prime_4282897 : Nat.Prime 4282897 := by
  apply nodeValid_prime [2, 3, 89227] ⟨4282897, 5, [(2, 4), (3, 1), (89227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89227
  · decide +kernel

theorem prime_4394113 : Nat.Prime 4394113 := by
  apply nodeValid_prime [2, 3, 11443] ⟨4394113, 5, [(2, 7), (3, 1), (11443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11443
  · decide +kernel

theorem prime_4967087 : Nat.Prime 4967087 := by
  apply nodeValid_prime [2, 2483543] ⟨4967087, 5, [(2, 1), (2483543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2483543
  · decide +kernel

theorem prime_5132273 : Nat.Prime 5132273 := by
  apply nodeValid_prime [2, 320767] ⟨5132273, 3, [(2, 4), (320767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_320767
  · decide +kernel

theorem prime_5173867 : Nat.Prime 5173867 := by
  apply nodeValid_prime [2, 3, 287437] ⟨5173867, 5, [(2, 1), (3, 2), (287437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_287437
  · decide +kernel

theorem prime_5257331 : Nat.Prime 5257331 := by
  apply nodeValid_prime [2, 5, 13, 37, 1093] ⟨5257331, 2, [(2, 1), (5, 1), (13, 1), (37, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_1093
  · decide +kernel

theorem prime_5517871 : Nat.Prime 5517871 := by
  apply nodeValid_prime [2, 3, 5, 193, 953] ⟨5517871, 6, [(2, 1), (3, 1), (5, 1), (193, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_193
    · exact prime_953
  · decide +kernel

theorem prime_5570767 : Nat.Prime 5570767 := by
  apply nodeValid_prime [2, 3, 197, 1571] ⟨5570767, 3, [(2, 1), (3, 2), (197, 1), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1571
  · decide +kernel

theorem prime_5939491 : Nat.Prime 5939491 := by
  apply nodeValid_prime [2, 3, 5, 29, 6827] ⟨5939491, 12, [(2, 1), (3, 1), (5, 1), (29, 1), (6827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_6827
  · decide +kernel

theorem prime_5972851 : Nat.Prime 5972851 := by
  apply nodeValid_prime [2, 3, 5, 13, 1021] ⟨5972851, 11, [(2, 1), (3, 2), (5, 2), (13, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1021
  · decide +kernel

theorem prime_6349169 : Nat.Prime 6349169 := by
  apply nodeValid_prime [2, 7, 83, 683] ⟨6349169, 3, [(2, 4), (7, 1), (83, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
    · exact prime_683
  · decide +kernel

theorem prime_7686271 : Nat.Prime 7686271 := by
  apply nodeValid_prime [2, 3, 5, 41, 2083] ⟨7686271, 3, [(2, 1), (3, 2), (5, 1), (41, 1), (2083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_2083
  · decide +kernel

theorem prime_9238699 : Nat.Prime 9238699 := by
  apply nodeValid_prime [2, 3, 7, 8147] ⟨9238699, 2, [(2, 1), (3, 4), (7, 1), (8147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8147
  · decide +kernel

theorem prime_9503107 : Nat.Prime 9503107 := by
  apply nodeValid_prime [2, 3, 1583851] ⟨9503107, 2, [(2, 1), (3, 1), (1583851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1583851
  · decide +kernel

theorem prime_10281431 : Nat.Prime 10281431 := by
  apply nodeValid_prime [2, 5, 17, 197, 307] ⟨10281431, 29, [(2, 1), (5, 1), (17, 1), (197, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_197
    · exact prime_307
  · decide +kernel

theorem prime_10376741 : Nat.Prime 10376741 := by
  apply nodeValid_prime [2, 5, 11, 101, 467] ⟨10376741, 3, [(2, 2), (5, 1), (11, 1), (101, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_101
    · exact prime_467
  · decide +kernel

theorem prime_10585789 : Nat.Prime 10585789 := by
  apply nodeValid_prime [2, 3, 239, 3691] ⟨10585789, 6, [(2, 2), (3, 1), (239, 1), (3691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_3691
  · decide +kernel

theorem prime_13468423 : Nat.Prime 13468423 := by
  apply nodeValid_prime [2, 3, 11, 204067] ⟨13468423, 5, [(2, 1), (3, 1), (11, 1), (204067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_204067
  · decide +kernel

theorem prime_14070593 : Nat.Prime 14070593 := by
  apply nodeValid_prime [2, 109, 2017] ⟨14070593, 3, [(2, 6), (109, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_2017
  · decide +kernel

theorem prime_14782189 : Nat.Prime 14782189 := by
  apply nodeValid_prime [2, 3, 89, 13841] ⟨14782189, 6, [(2, 2), (3, 1), (89, 1), (13841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_13841
  · decide +kernel

theorem prime_17131589 : Nat.Prime 17131589 := by
  apply nodeValid_prime [2, 4282897] ⟨17131589, 2, [(2, 2), (4282897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4282897
  · decide +kernel

theorem prime_17874821 : Nat.Prime 17874821 := by
  apply nodeValid_prime [2, 5, 17, 19, 2767] ⟨17874821, 2, [(2, 2), (5, 1), (17, 1), (19, 1), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_2767
  · decide +kernel

theorem prime_20562863 : Nat.Prime 20562863 := by
  apply nodeValid_prime [2, 10281431] ⟨20562863, 5, [(2, 1), (10281431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10281431
  · decide +kernel

theorem prime_22283069 : Nat.Prime 22283069 := by
  apply nodeValid_prime [2, 5570767] ⟨22283069, 2, [(2, 2), (5570767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5570767
  · decide +kernel

theorem prime_30793639 : Nat.Prime 30793639 := by
  apply nodeValid_prime [2, 3, 5132273] ⟨30793639, 3, [(2, 1), (3, 1), (5132273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5132273
  · decide +kernel

theorem prime_41125727 : Nat.Prime 41125727 := by
  apply nodeValid_prime [2, 20562863] ⟨41125727, 5, [(2, 1), (20562863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20562863
  · decide +kernel

theorem prime_41158217 : Nat.Prime 41158217 := by
  apply nodeValid_prime [2, 11, 113, 4139] ⟨41158217, 3, [(2, 3), (11, 1), (113, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
    · exact prime_4139
  · decide +kernel

theorem prime_42343157 : Nat.Prime 42343157 := by
  apply nodeValid_prime [2, 10585789] ⟨42343157, 2, [(2, 2), (10585789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10585789
  · decide +kernel

theorem prime_47488117 : Nat.Prime 47488117 := by
  apply nodeValid_prime [2, 3, 13, 304411] ⟨47488117, 2, [(2, 2), (3, 1), (13, 1), (304411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_304411
  · decide +kernel

theorem prime_51148091 : Nat.Prime 51148091 := by
  apply nodeValid_prime [2, 5, 7, 23, 31769] ⟨51148091, 2, [(2, 1), (5, 1), (7, 1), (23, 1), (31769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_31769
  · decide +kernel

theorem prime_53873693 : Nat.Prime 53873693 := by
  apply nodeValid_prime [2, 13468423] ⟨53873693, 2, [(2, 2), (13468423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13468423
  · decide +kernel

theorem prime_59728511 : Nat.Prime 59728511 := by
  apply nodeValid_prime [2, 5, 5972851] ⟨59728511, 13, [(2, 1), (5, 1), (5972851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5972851
  · decide +kernel

theorem prime_62260447 : Nat.Prime 62260447 := by
  apply nodeValid_prime [2, 3, 10376741] ⟨62260447, 3, [(2, 1), (3, 1), (10376741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10376741
  · decide +kernel

theorem prime_70139437 : Nat.Prime 70139437 := by
  apply nodeValid_prime [2, 3, 59, 157, 631] ⟨70139437, 2, [(2, 2), (3, 1), (59, 1), (157, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_157
    · exact prime_631
  · decide +kernel

theorem prime_96437221 : Nat.Prime 96437221 := by
  apply nodeValid_prime [2, 3, 5, 11, 146117] ⟨96437221, 17, [(2, 2), (3, 1), (5, 1), (11, 1), (146117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_146117
  · decide +kernel

theorem prime_152839891 : Nat.Prime 152839891 := by
  apply nodeValid_prime [2, 3, 5, 7, 242603] ⟨152839891, 7, [(2, 1), (3, 2), (5, 1), (7, 1), (242603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_242603
  · decide +kernel

theorem prime_202034713 : Nat.Prime 202034713 := by
  apply nodeValid_prime [2, 3, 11, 765283] ⟨202034713, 7, [(2, 3), (3, 1), (11, 1), (765283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_765283
  · decide +kernel

theorem prime_218259463 : Nat.Prime 218259463 := by
  apply nodeValid_prime [2, 3, 79, 460463] ⟨218259463, 3, [(2, 1), (3, 1), (79, 1), (460463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_460463
  · decide +kernel

theorem prime_220807903 : Nat.Prime 220807903 := by
  apply nodeValid_prime [2, 3, 7, 5257331] ⟨220807903, 3, [(2, 1), (3, 1), (7, 1), (5257331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5257331
  · decide +kernel

theorem prime_246754363 : Nat.Prime 246754363 := by
  apply nodeValid_prime [2, 3, 41125727] ⟨246754363, 3, [(2, 1), (3, 1), (41125727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41125727
  · decide +kernel

theorem prime_264117961 : Nat.Prime 264117961 := by
  apply nodeValid_prime [2, 3, 5, 157, 4673] ⟨264117961, 23, [(2, 3), (3, 2), (5, 1), (157, 1), (4673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
    · exact prime_4673
  · decide +kernel

theorem prime_267890713 : Nat.Prime 267890713 := by
  apply nodeValid_prime [2, 3, 89, 167, 751] ⟨267890713, 7, [(2, 3), (3, 1), (89, 1), (167, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_167
    · exact prime_751
  · decide +kernel

theorem prime_306102241 : Nat.Prime 306102241 := by
  apply nodeValid_prime [2, 3, 5, 7873] ⟨306102241, 17, [(2, 5), (3, 5), (5, 1), (7873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7873
  · decide +kernel

theorem prime_306799121 : Nat.Prime 306799121 := by
  apply nodeValid_prime [2, 5, 29, 132241] ⟨306799121, 3, [(2, 4), (5, 1), (29, 1), (132241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_132241
  · decide +kernel

theorem prime_456149137 : Nat.Prime 456149137 := by
  apply nodeValid_prime [2, 3, 9503107] ⟨456149137, 5, [(2, 4), (3, 1), (9503107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9503107
  · decide +kernel

theorem prime_502594427 : Nat.Prime 502594427 := by
  apply nodeValid_prime [2, 17, 14782189] ⟨502594427, 2, [(2, 1), (17, 1), (14782189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_14782189
  · decide +kernel

theorem prime_543928303 : Nat.Prime 543928303 := by
  apply nodeValid_prime [2, 3, 71, 425609] ⟨543928303, 3, [(2, 1), (3, 2), (71, 1), (425609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_425609
  · decide +kernel

theorem prime_1085092727 : Nat.Prime 1085092727 := by
  apply nodeValid_prime [2, 503, 1009, 1069] ⟨1085092727, 5, [(2, 1), (503, 1), (1009, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_503
    · exact prime_1009
    · exact prime_1069
  · decide +kernel

theorem prime_1114153451 : Nat.Prime 1114153451 := by
  apply nodeValid_prime [2, 5, 22283069] ⟨1114153451, 2, [(2, 1), (5, 2), (22283069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22283069
  · decide +kernel

theorem prime_1342676627 : Nat.Prime 1342676627 := by
  apply nodeValid_prime [2, 17, 29, 1361741] ⟨1342676627, 2, [(2, 1), (17, 1), (29, 1), (1361741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_1361741
  · decide +kernel

theorem prime_1424643511 : Nat.Prime 1424643511 := by
  apply nodeValid_prime [2, 3, 5, 47488117] ⟨1424643511, 3, [(2, 1), (3, 1), (5, 1), (47488117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47488117
  · decide +kernel

theorem prime_1644325559 : Nat.Prime 1644325559 := by
  apply nodeValid_prime [2, 149, 5517871] ⟨1644325559, 7, [(2, 1), (149, 1), (5517871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_5517871
  · decide +kernel

theorem prime_1964770651 : Nat.Prime 1964770651 := by
  apply nodeValid_prime [2, 3, 5, 1181, 3697] ⟨1964770651, 3, [(2, 1), (3, 2), (5, 2), (1181, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1181
    · exact prime_3697
  · decide +kernel

theorem prime_2194748063 : Nat.Prime 2194748063 := by
  apply nodeValid_prime [2, 13, 131, 644377] ⟨2194748063, 5, [(2, 1), (13, 1), (131, 1), (644377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_131
    · exact prime_644377
  · decide +kernel

theorem prime_2486752273 : Nat.Prime 2486752273 := by
  apply nodeValid_prime [2, 3, 23, 353, 709] ⟨2486752273, 5, [(2, 4), (3, 3), (23, 1), (353, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_353
    · exact prime_709
  · decide +kernel

theorem prime_2729695043 : Nat.Prime 2729695043 := by
  apply nodeValid_prime [2, 97, 14070593] ⟨2729695043, 2, [(2, 1), (97, 1), (14070593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_14070593
  · decide +kernel

theorem prime_2961052357 : Nat.Prime 2961052357 := by
  apply nodeValid_prime [2, 3, 246754363] ⟨2961052357, 2, [(2, 2), (3, 1), (246754363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_246754363
  · decide +kernel

theorem prime_3492151409 : Nat.Prime 3492151409 := by
  apply nodeValid_prime [2, 218259463] ⟨3492151409, 3, [(2, 4), (218259463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_218259463
  · decide +kernel

theorem prime_7367709319 : Nat.Prime 7367709319 := by
  apply nodeValid_prime [2, 3, 29, 42343157] ⟨7367709319, 17, [(2, 1), (3, 1), (29, 1), (42343157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_42343157
  · decide +kernel

theorem prime_11712635149 : Nat.Prime 11712635149 := by
  apply nodeValid_prime [2, 3, 41, 53, 449173] ⟨11712635149, 7, [(2, 2), (3, 1), (41, 1), (53, 1), (449173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_53
    · exact prime_449173
  · decide +kernel

theorem prime_15195719519 : Nat.Prime 15195719519 := by
  apply nodeValid_prime [2, 7, 17, 43, 1484827] ⟨15195719519, 13, [(2, 1), (7, 1), (17, 1), (43, 1), (1484827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_1484827
  · decide +kernel

theorem prime_49329766771 : Nat.Prime 49329766771 := by
  apply nodeValid_prime [2, 3, 5, 1644325559] ⟨49329766771, 2, [(2, 1), (3, 1), (5, 1), (1644325559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1644325559
  · decide +kernel

theorem prime_51941536289 : Nat.Prime 51941536289 := by
  apply nodeValid_prime [2, 397, 1291, 3167] ⟨51941536289, 3, [(2, 5), (397, 1), (1291, 1), (3167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_1291
    · exact prime_3167
  · decide +kernel

theorem prime_63644332693 : Nat.Prime 63644332693 := by
  apply nodeValid_prime [2, 3, 17, 71, 4394113] ⟨63644332693, 5, [(2, 2), (3, 1), (17, 1), (71, 1), (4394113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_71
    · exact prime_4394113
  · decide +kernel

theorem prime_76734070129 : Nat.Prime 76734070129 := by
  apply nodeValid_prime [2, 3, 467, 1141061] ⟨76734070129, 7, [(2, 4), (3, 2), (467, 1), (1141061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_1141061
  · decide +kernel

theorem prime_133465807537 : Nat.Prime 133465807537 := by
  apply nodeValid_prime [2, 3, 1931, 1439947] ⟨133465807537, 5, [(2, 4), (3, 1), (1931, 1), (1439947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1931
    · exact prime_1439947
  · decide +kernel

theorem prime_134695306453 : Nat.Prime 134695306453 := by
  apply nodeValid_prime [2, 3, 7, 233, 2113, 3257] ⟨134695306453, 6, [(2, 2), (3, 1), (7, 1), (233, 1), (2113, 1), (3257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_233
    · exact prime_2113
    · exact prime_3257
  · decide +kernel

theorem prime_182348634229 : Nat.Prime 182348634229 := by
  apply nodeValid_prime [2, 3, 15195719519] ⟨182348634229, 10, [(2, 2), (3, 1), (15195719519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15195719519
  · decide +kernel

theorem prime_359553027083 : Nat.Prime 359553027083 := by
  apply nodeValid_prime [2, 47, 71, 53873693] ⟨359553027083, 2, [(2, 1), (47, 1), (71, 1), (53873693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_71
    · exact prime_53873693
  · decide +kernel

theorem prime_362118951331 : Nat.Prime 362118951331 := by
  apply nodeValid_prime [2, 3, 5, 2333, 5173867] ⟨362118951331, 7, [(2, 1), (3, 1), (5, 1), (2333, 1), (5173867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2333
    · exact prime_5173867
  · decide +kernel

theorem prime_537138490969 : Nat.Prime 537138490969 := by
  apply nodeValid_prime [2, 3, 2486752273] ⟨537138490969, 7, [(2, 3), (3, 3), (2486752273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2486752273
  · decide +kernel

theorem prime_1077562451489 : Nat.Prime 1077562451489 := by
  apply nodeValid_prime [2, 67, 502594427] ⟨1077562451489, 3, [(2, 5), (67, 1), (502594427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_502594427
  · decide +kernel

theorem prime_1085254868963 : Nat.Prime 1085254868963 := by
  apply nodeValid_prime [2, 11, 49329766771] ⟨1085254868963, 2, [(2, 1), (11, 1), (49329766771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_49329766771
  · decide +kernel

theorem prime_1090772280659 : Nat.Prime 1090772280659 := by
  apply nodeValid_prime [2, 89, 199, 30793639] ⟨1090772280659, 2, [(2, 1), (89, 1), (199, 1), (30793639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_199
    · exact prime_30793639
  · decide +kernel

theorem prime_2135452920593 : Nat.Prime 2135452920593 := by
  apply nodeValid_prime [2, 133465807537] ⟨2135452920593, 3, [(2, 4), (133465807537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_133465807537
  · decide +kernel

theorem prime_2135452930151 : Nat.Prime 2135452930151 := by
  apply nodeValid_prime [2, 5, 43, 5701, 174221] ⟨2135452930151, 7, [(2, 1), (5, 2), (43, 1), (5701, 1), (174221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_5701
    · exact prime_174221
  · decide +kernel

theorem prime_2135452930829 : Nat.Prime 2135452930829 := by
  apply nodeValid_prime [2, 7, 17, 109, 41158217] ⟨2135452930829, 3, [(2, 2), (7, 1), (17, 1), (109, 1), (41158217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_109
    · exact prime_41158217
  · decide +kernel

theorem prime_2137632672191 : Nat.Prime 2137632672191 := by
  apply nodeValid_prime [2, 5, 197, 1085092727] ⟨2137632672191, 7, [(2, 1), (5, 1), (197, 1), (1085092727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_197
    · exact prime_1085092727
  · decide +kernel

theorem prime_2137632737609 : Nat.Prime 2137632737609 := by
  apply nodeValid_prime [2, 157, 3779, 450367] ⟨2137632737609, 3, [(2, 3), (157, 1), (3779, 1), (450367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_3779
    · exact prime_450367
  · decide +kernel

theorem prime_2137632738671 : Nat.Prime 2137632738671 := by
  apply nodeValid_prime [2, 5, 11, 13, 41, 254963] ⟨2137632738671, 11, [(2, 1), (5, 1), (11, 2), (13, 2), (41, 1), (254963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_41
    · exact prime_254963
  · decide +kernel

theorem prime_2139813926441 : Nat.Prime 2139813926441 := by
  apply nodeValid_prime [2, 5, 83, 1123, 573929] ⟨2139813926441, 3, [(2, 3), (5, 1), (83, 1), (1123, 1), (573929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_1123
    · exact prime_573929
  · decide +kernel

theorem prime_2139813943997 : Nat.Prime 2139813943997 := by
  apply nodeValid_prime [2, 29, 263, 70139437] ⟨2139813943997, 2, [(2, 2), (29, 1), (263, 1), (70139437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_263
    · exact prime_70139437
  · decide +kernel

theorem prime_2139813944003 : Nat.Prime 2139813944003 := by
  apply nodeValid_prime [2, 7, 281, 543928303] ⟨2139813944003, 5, [(2, 1), (7, 1), (281, 1), (543928303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_281
    · exact prime_543928303
  · decide +kernel

theorem prime_2141996663707 : Nat.Prime 2141996663707 := by
  apply nodeValid_prime [2, 3, 41, 1753, 4967087] ⟨2141996663707, 3, [(2, 1), (3, 1), (41, 1), (1753, 1), (4967087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1753
    · exact prime_4967087
  · decide +kernel

theorem prime_2141996663711 : Nat.Prime 2141996663711 := by
  apply nodeValid_prime [2, 5, 811, 264117961] ⟨2141996663711, 7, [(2, 1), (5, 1), (811, 1), (264117961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_811
    · exact prime_264117961
  · decide +kernel

theorem prime_2141996682883 : Nat.Prime 2141996682883 := by
  apply nodeValid_prime [2, 3, 7, 6343, 1148621] ⟨2141996682883, 3, [(2, 1), (3, 1), (7, 2), (6343, 1), (1148621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6343
    · exact prime_1148621
  · decide +kernel

theorem prime_2144180949311 : Nat.Prime 2144180949311 := by
  apply nodeValid_prime [2, 5, 103, 11689, 178093] ⟨2144180949311, 7, [(2, 1), (5, 1), (103, 1), (11689, 1), (178093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_11689
    · exact prime_178093
  · decide +kernel

theorem prime_2144180965127 : Nat.Prime 2144180965127 := by
  apply nodeValid_prime [2, 307, 3492151409] ⟨2144180965127, 5, [(2, 1), (307, 1), (3492151409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_3492151409
  · decide +kernel

theorem prime_2144180965639 : Nat.Prime 2144180965639 := by
  apply nodeValid_prime [2, 3, 283, 12577, 100403] ⟨2144180965639, 3, [(2, 1), (3, 1), (283, 1), (12577, 1), (100403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_12577
    · exact prime_100403
  · decide +kernel

theorem prime_2146366649879 : Nat.Prime 2146366649879 := by
  apply nodeValid_prime [2, 11, 1567, 62260447] ⟨2146366649879, 7, [(2, 1), (11, 1), (1567, 1), (62260447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1567
    · exact prime_62260447
  · decide +kernel

theorem prime_2146366650517 : Nat.Prime 2146366650517 := by
  apply nodeValid_prime [2, 3, 11, 53, 306799121] ⟨2146366650517, 6, [(2, 2), (3, 1), (11, 1), (53, 1), (306799121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_306799121
  · decide +kernel

theorem prime_2146366721113 : Nat.Prime 2146366721113 := by
  apply nodeValid_prime [2, 3, 41, 53, 59, 167, 4177] ⟨2146366721113, 5, [(2, 3), (3, 1), (41, 1), (53, 1), (59, 1), (167, 1), (4177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_53
    · exact prime_59
    · exact prime_167
    · exact prime_4177
  · decide +kernel

theorem prime_2148553963613 : Nat.Prime 2148553963613 := by
  apply nodeValid_prime [2, 7, 76734070129] ⟨2148553963613, 2, [(2, 2), (7, 1), (76734070129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_76734070129
  · decide +kernel

theorem prime_2148553963877 : Nat.Prime 2148553963877 := by
  apply nodeValid_prime [2, 537138490969] ⟨2148553963877, 2, [(2, 2), (537138490969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_537138490969
  · decide +kernel

theorem prime_2148553997693 : Nat.Prime 2148553997693 := by
  apply nodeValid_prime [2, 17, 23, 59728511] ⟨2148553997693, 2, [(2, 2), (17, 1), (23, 2), (59728511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_59728511
  · decide +kernel

theorem prime_2150742780533 : Nat.Prime 2150742780533 := by
  apply nodeValid_prime [2, 31, 727, 1987, 12007] ⟨2150742780533, 3, [(2, 2), (31, 1), (727, 1), (1987, 1), (12007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_727
    · exact prime_1987
    · exact prime_12007
  · decide +kernel

theorem prime_2150742902743 : Nat.Prime 2150742902743 := by
  apply nodeValid_prime [2, 3, 7, 59, 96437221] ⟨2150742902743, 5, [(2, 1), (3, 3), (7, 1), (59, 1), (96437221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_96437221
  · decide +kernel

theorem prime_2150742903737 : Nat.Prime 2150742903737 := by
  apply nodeValid_prime [2, 7, 23, 263, 6349169] ⟨2150742903737, 3, [(2, 3), (7, 1), (23, 1), (263, 1), (6349169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_263
    · exact prime_6349169
  · decide +kernel

theorem prime_2152933068973 : Nat.Prime 2152933068973 := by
  apply nodeValid_prime [2, 3, 7, 19, 149, 1597, 5669] ⟨2152933068973, 13, [(2, 2), (3, 1), (7, 1), (19, 1), (149, 1), (1597, 1), (5669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_149
    · exact prime_1597
    · exact prime_5669
  · decide +kernel

theorem prime_2152933081469 : Nat.Prime 2152933081469 := by
  apply nodeValid_prime [2, 13, 293, 1163, 121501] ⟨2152933081469, 2, [(2, 2), (13, 1), (293, 1), (1163, 1), (121501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_293
    · exact prime_1163
    · exact prime_121501
  · decide +kernel

theorem prime_2152933081751 : Nat.Prime 2152933081751 := by
  apply nodeValid_prime [2, 5, 11, 31, 1381, 18287] ⟨2152933081751, 7, [(2, 1), (5, 3), (11, 1), (31, 1), (1381, 1), (18287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_1381
    · exact prime_18287
  · decide +kernel

theorem prime_2155124867417 : Nat.Prime 2155124867417 := by
  apply nodeValid_prime [2, 23, 11712635149] ⟨2155124867417, 3, [(2, 3), (23, 1), (11712635149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_11712635149
  · decide +kernel

theorem prime_2155124902979 : Nat.Prime 2155124902979 := by
  apply nodeValid_prime [2, 1077562451489] ⟨2155124902979, 2, [(2, 1), (1077562451489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1077562451489
  · decide +kernel

theorem prime_2155124903249 : Nat.Prime 2155124903249 := by
  apply nodeValid_prime [2, 134695306453] ⟨2155124903249, 3, [(2, 4), (134695306453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_134695306453
  · decide +kernel

theorem prime_2157318162499 : Nat.Prime 2157318162499 := by
  apply nodeValid_prime [2, 3, 359553027083] ⟨2157318162499, 3, [(2, 1), (3, 1), (359553027083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359553027083
  · decide +kernel

theorem prime_2157318163057 : Nat.Prime 2157318163057 := by
  apply nodeValid_prime [2, 3, 7, 23, 47, 5939491] ⟨2157318163057, 5, [(2, 4), (3, 1), (7, 1), (23, 1), (47, 1), (5939491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_47
    · exact prime_5939491
  · decide +kernel

theorem prime_2157318174799 : Nat.Prime 2157318174799 := by
  apply nodeValid_prime [2, 3, 61, 1964770651] ⟨2157318174799, 3, [(2, 1), (3, 2), (61, 1), (1964770651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_1964770651
  · decide +kernel

theorem prime_2159512991497 : Nat.Prime 2159512991497 := by
  apply nodeValid_prime [2, 3, 7, 29, 1021, 2297] ⟨2159512991497, 5, [(2, 3), (3, 4), (7, 2), (29, 1), (1021, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_1021
    · exact prime_2297
  · decide +kernel

theorem prime_2159513057417 : Nat.Prime 2159513057417 := by
  apply nodeValid_prime [2, 11, 13, 17, 37, 47, 63853] ⟨2159513057417, 5, [(2, 3), (11, 1), (13, 1), (17, 1), (37, 1), (47, 1), (63853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_37
    · exact prime_47
    · exact prime_63853
  · decide +kernel

theorem prime_2159513057809 : Nat.Prime 2159513057809 := by
  apply nodeValid_prime [2, 3, 191, 257, 101837] ⟨2159513057809, 11, [(2, 4), (3, 3), (191, 1), (257, 1), (101837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_257
    · exact prime_101837
  · decide +kernel

theorem prime_2161709327441 : Nat.Prime 2161709327441 := by
  apply nodeValid_prime [2, 5, 13, 67, 383, 81001] ⟨2161709327441, 3, [(2, 4), (5, 1), (13, 1), (67, 1), (383, 1), (81001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_67
    · exact prime_383
    · exact prime_81001
  · decide +kernel

theorem prime_2161709369471 : Nat.Prime 2161709369471 := by
  apply nodeValid_prime [2, 5, 7, 23, 1342676627] ⟨2161709369471, 7, [(2, 1), (5, 1), (7, 1), (23, 1), (1342676627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_1342676627
  · decide +kernel

theorem prime_2161709370371 : Nat.Prime 2161709370371 := by
  apply nodeValid_prime [2, 5, 11, 89, 220807903] ⟨2161709370371, 6, [(2, 1), (5, 1), (11, 1), (89, 1), (220807903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_89
    · exact prime_220807903
  · decide +kernel

theorem prime_2163907176779 : Nat.Prime 2163907176779 := by
  apply nodeValid_prime [2, 7079, 152839891] ⟨2163907176779, 2, [(2, 1), (7079, 1), (152839891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7079
    · exact prime_152839891
  · decide +kernel

theorem prime_2163907311521 : Nat.Prime 2163907311521 := by
  apply nodeValid_prime [2, 5, 53, 857, 297757] ⟨2163907311521, 3, [(2, 5), (5, 1), (53, 1), (857, 1), (297757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_857
    · exact prime_297757
  · decide +kernel

theorem prime_2163907311563 : Nat.Prime 2163907311563 := by
  apply nodeValid_prime [2, 17, 63644332693] ⟨2163907311563, 2, [(2, 1), (17, 1), (63644332693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_63644332693
  · decide +kernel

theorem prime_2166106539787 : Nat.Prime 2166106539787 := by
  apply nodeValid_prime [2, 3, 7, 7367709319] ⟨2166106539787, 11, [(2, 1), (3, 1), (7, 2), (7367709319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7367709319
  · decide +kernel

theorem prime_2166106558423 : Nat.Prime 2166106558423 := by
  apply nodeValid_prime [2, 3, 19, 1063, 17874821] ⟨2166106558423, 3, [(2, 1), (3, 1), (19, 1), (1063, 1), (17874821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1063
    · exact prime_17874821
  · decide +kernel

theorem prime_2166106558831 : Nat.Prime 2166106558831 := by
  apply nodeValid_prime [2, 3, 5, 257, 307, 915139] ⟨2166106558831, 3, [(2, 1), (3, 1), (5, 1), (257, 1), (307, 1), (915139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
    · exact prime_307
    · exact prime_915139
  · decide +kernel

theorem prime_2168307423743 : Nat.Prime 2168307423743 := by
  apply nodeValid_prime [2, 761, 1424643511] ⟨2168307423743, 5, [(2, 1), (761, 1), (1424643511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_761
    · exact prime_1424643511
  · decide +kernel

theorem prime_2168307431023 : Nat.Prime 2168307431023 := by
  apply nodeValid_prime [2, 3, 19, 71, 267890713] ⟨2168307431023, 3, [(2, 1), (3, 1), (19, 1), (71, 1), (267890713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_71
    · exact prime_267890713
  · decide +kernel

theorem prime_2168307432251 : Nat.Prime 2168307432251 := by
  apply nodeValid_prime [2, 5, 491, 1361, 12979] ⟨2168307432251, 2, [(2, 1), (5, 3), (491, 1), (1361, 1), (12979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_491
    · exact prime_1361
    · exact prime_12979
  · decide +kernel

theorem prime_2170509735343 : Nat.Prime 2170509735343 := by
  apply nodeValid_prime [2, 3, 13, 241, 719, 160591] ⟨2170509735343, 3, [(2, 1), (3, 1), (13, 1), (241, 1), (719, 1), (160591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_241
    · exact prime_719
    · exact prime_160591
  · decide +kernel

theorem prime_2170509737927 : Nat.Prime 2170509737927 := by
  apply nodeValid_prime [2, 1085254868963] ⟨2170509737927, 5, [(2, 1), (1085254868963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1085254868963
  · decide +kernel

theorem prime_2170509809827 : Nat.Prime 2170509809827 := by
  apply nodeValid_prime [2, 3, 137, 1163, 2270441] ⟨2170509809827, 2, [(2, 1), (3, 1), (137, 1), (1163, 1), (2270441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_1163
    · exact prime_2270441
  · decide +kernel

theorem prime_2172713706619 : Nat.Prime 2172713706619 := by
  apply nodeValid_prime [2, 3, 7, 13, 306102241] ⟨2172713706619, 2, [(2, 1), (3, 1), (7, 1), (13, 2), (306102241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_306102241
  · decide +kernel

theorem prime_2172713707987 : Nat.Prime 2172713707987 := by
  apply nodeValid_prime [2, 3, 362118951331] ⟨2172713707987, 3, [(2, 1), (3, 1), (362118951331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_362118951331
  · decide +kernel

theorem prime_2172713708981 : Nat.Prime 2172713708981 := by
  apply nodeValid_prime [2, 5, 32579, 3334531] ⟨2172713708981, 2, [(2, 2), (5, 1), (32579, 1), (3334531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_32579
    · exact prime_3334531
  · decide +kernel

theorem prime_2174919085217 : Nat.Prime 2174919085217 := by
  apply nodeValid_prime [2, 149, 456149137] ⟨2174919085217, 3, [(2, 5), (149, 1), (456149137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_456149137
  · decide +kernel

theorem prime_2174919086387 : Nat.Prime 2174919086387 := by
  apply nodeValid_prime [2, 31, 3797, 9238699] ⟨2174919086387, 2, [(2, 1), (31, 1), (3797, 1), (9238699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3797
    · exact prime_9238699
  · decide +kernel

theorem prime_2174919125503 : Nat.Prime 2174919125503 := by
  apply nodeValid_prime [2, 3, 19, 373, 51148091] ⟨2174919125503, 11, [(2, 1), (3, 1), (19, 1), (373, 1), (51148091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_373
    · exact prime_51148091
  · decide +kernel

theorem prime_2177126067289 : Nat.Prime 2177126067289 := by
  apply nodeValid_prime [2, 3, 449, 202034713] ⟨2177126067289, 7, [(2, 3), (3, 1), (449, 1), (202034713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
    · exact prime_202034713
  · decide +kernel

theorem prime_2177126091073 : Nat.Prime 2177126091073 := by
  apply nodeValid_prime [2, 3, 101, 3259, 11483] ⟨2177126091073, 5, [(2, 6), (3, 2), (101, 1), (3259, 1), (11483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_3259
    · exact prime_11483
  · decide +kernel

theorem prime_2177126091137 : Nat.Prime 2177126091137 := by
  apply nodeValid_prime [2, 19, 20693, 43261] ⟨2177126091137, 3, [(2, 7), (19, 1), (20693, 1), (43261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_20693
    · exact prime_43261
  · decide +kernel

theorem prime_2179334534257 : Nat.Prime 2179334534257 := by
  apply nodeValid_prime [2, 3, 11, 179, 7686271] ⟨2179334534257, 7, [(2, 4), (3, 2), (11, 1), (179, 1), (7686271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_179
    · exact prime_7686271
  · decide +kernel

theorem prime_2179334534753 : Nat.Prime 2179334534753 := by
  apply nodeValid_prime [2, 23, 2961052357] ⟨2179334534753, 3, [(2, 5), (23, 1), (2961052357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2961052357
  · decide +kernel

theorem prime_2179334536861 : Nat.Prime 2179334536861 := by
  apply nodeValid_prime [2, 3, 5, 13, 2203, 1268279] ⟨2179334536861, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (2203, 1), (1268279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_2203
    · exact prime_1268279
  · decide +kernel

theorem prime_2181544524139 : Nat.Prime 2181544524139 := by
  apply nodeValid_prime [2, 3, 7, 51941536289] ⟨2181544524139, 2, [(2, 1), (3, 1), (7, 1), (51941536289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_51941536289
  · decide +kernel

theorem prime_2181544559819 : Nat.Prime 2181544559819 := by
  apply nodeValid_prime [2, 13, 41, 17627, 116099] ⟨2181544559819, 6, [(2, 1), (13, 1), (41, 1), (17627, 1), (116099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_17627
    · exact prime_116099
  · decide +kernel

theorem prime_2181544561319 : Nat.Prime 2181544561319 := by
  apply nodeValid_prime [2, 1090772280659] ⟨2181544561319, 7, [(2, 1), (1090772280659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1090772280659
  · decide +kernel

theorem prime_2183756034401 : Nat.Prime 2183756034401 := by
  apply nodeValid_prime [2, 5, 2729695043] ⟨2183756034401, 3, [(2, 5), (5, 2), (2729695043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2729695043
  · decide +kernel

theorem prime_2183756034547 : Nat.Prime 2183756034547 := by
  apply nodeValid_prime [2, 3, 19, 41, 113, 863, 1597] ⟨2183756034547, 2, [(2, 1), (3, 2), (19, 1), (41, 1), (113, 1), (863, 1), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_113
    · exact prime_863
    · exact prime_1597
  · decide +kernel

theorem prime_2183756041151 : Nat.Prime 2183756041151 := by
  apply nodeValid_prime [2, 5, 49297, 885959] ⟨2183756041151, 11, [(2, 1), (5, 2), (49297, 1), (885959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49297
    · exact prime_885959
  · decide +kernel

theorem prime_2185969068671 : Nat.Prime 2185969068671 := by
  apply nodeValid_prime [2, 5, 67, 5573, 585437] ⟨2185969068671, 13, [(2, 1), (5, 1), (67, 1), (5573, 1), (585437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_5573
    · exact prime_585437
  · decide +kernel

theorem prime_2185969070749 : Nat.Prime 2185969070749 := by
  apply nodeValid_prime [2, 3, 83, 2194748063] ⟨2185969070749, 14, [(2, 2), (3, 1), (83, 1), (2194748063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_2194748063
  · decide +kernel

theorem prime_2185969070863 : Nat.Prime 2185969070863 := by
  apply nodeValid_prime [2, 3, 109, 1114153451] ⟨2185969070863, 3, [(2, 1), (3, 2), (109, 1), (1114153451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1114153451
  · decide +kernel

theorem prime_2188183599793 : Nat.Prime 2188183599793 := by
  apply nodeValid_prime [2, 3, 887, 17131589] ⟨2188183599793, 10, [(2, 4), (3, 2), (887, 1), (17131589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_887
    · exact prime_17131589
  · decide +kernel

theorem prime_2188183610749 : Nat.Prime 2188183610749 := by
  apply nodeValid_prime [2, 3, 182348634229] ⟨2188183610749, 2, [(2, 2), (3, 1), (182348634229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_182348634229
  · decide +kernel

end Sude.Lucas.Generated
