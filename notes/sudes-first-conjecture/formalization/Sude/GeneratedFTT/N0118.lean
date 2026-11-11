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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0111

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10531 : Nat.Prime 10531 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨10531, 3, [(2, 1), (3, 4), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_11897 : Nat.Prime 11897 := by
  apply nodeValid_prime [2, 1487] ⟨11897, 3, [(2, 3), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1487
  · decide +kernel

theorem prime_19289 : Nat.Prime 19289 := by
  apply nodeValid_prime [2, 2411] ⟨19289, 3, [(2, 3), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2411
  · decide +kernel

theorem prime_21227 : Nat.Prime 21227 := by
  apply nodeValid_prime [2, 10613] ⟨21227, 2, [(2, 1), (10613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10613
  · decide +kernel

theorem prime_22123 : Nat.Prime 22123 := by
  apply nodeValid_prime [2, 3, 1229] ⟨22123, 2, [(2, 1), (3, 2), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1229
  · decide +kernel

theorem prime_26407 : Nat.Prime 26407 := by
  apply nodeValid_prime [2, 3, 163] ⟨26407, 5, [(2, 1), (3, 4), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
  · decide +kernel

theorem prime_31267 : Nat.Prime 31267 := by
  apply nodeValid_prime [2, 3, 193] ⟨31267, 2, [(2, 1), (3, 4), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
  · decide +kernel

theorem prime_33923 : Nat.Prime 33923 := by
  apply nodeValid_prime [2, 7, 2423] ⟨33923, 2, [(2, 1), (7, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2423
  · decide +kernel

theorem prime_39667 : Nat.Prime 39667 := by
  apply nodeValid_prime [2, 3, 11, 601] ⟨39667, 3, [(2, 1), (3, 1), (11, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_601
  · decide +kernel

theorem prime_40841 : Nat.Prime 40841 := by
  apply nodeValid_prime [2, 5, 1021] ⟨40841, 3, [(2, 3), (5, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1021
  · decide +kernel

theorem prime_42397 : Nat.Prime 42397 := by
  apply nodeValid_prime [2, 3, 3533] ⟨42397, 2, [(2, 2), (3, 1), (3533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3533
  · decide +kernel

theorem prime_48491 : Nat.Prime 48491 := by
  apply nodeValid_prime [2, 5, 13, 373] ⟨48491, 2, [(2, 1), (5, 1), (13, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_373
  · decide +kernel

theorem prime_50873 : Nat.Prime 50873 := by
  apply nodeValid_prime [2, 6359] ⟨50873, 3, [(2, 3), (6359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6359
  · decide +kernel

theorem prime_58549 : Nat.Prime 58549 := by
  apply nodeValid_prime [2, 3, 7, 17, 41] ⟨58549, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_60449 : Nat.Prime 60449 := by
  apply nodeValid_prime [2, 1889] ⟨60449, 3, [(2, 5), (1889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1889
  · decide +kernel

theorem prime_61781 : Nat.Prime 61781 := by
  apply nodeValid_prime [2, 5, 3089] ⟨61781, 2, [(2, 2), (5, 1), (3089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3089
  · decide +kernel

theorem prime_71849 : Nat.Prime 71849 := by
  apply nodeValid_prime [2, 7, 1283] ⟨71849, 3, [(2, 3), (7, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1283
  · decide +kernel

theorem prime_81533 : Nat.Prime 81533 := by
  apply nodeValid_prime [2, 11, 17, 109] ⟨81533, 3, [(2, 2), (11, 1), (17, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_109
  · decide +kernel

theorem prime_82457 : Nat.Prime 82457 := by
  apply nodeValid_prime [2, 11, 937] ⟨82457, 3, [(2, 3), (11, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_937
  · decide +kernel

theorem prime_82889 : Nat.Prime 82889 := by
  apply nodeValid_prime [2, 13, 797] ⟨82889, 3, [(2, 3), (13, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_797
  · decide +kernel

theorem prime_84523 : Nat.Prime 84523 := by
  apply nodeValid_prime [2, 3, 14087] ⟨84523, 2, [(2, 1), (3, 1), (14087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14087
  · decide +kernel

theorem prime_87631 : Nat.Prime 87631 := by
  apply nodeValid_prime [2, 3, 5, 23, 127] ⟨87631, 6, [(2, 1), (3, 1), (5, 1), (23, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_127
  · decide +kernel

theorem prime_93809 : Nat.Prime 93809 := by
  apply nodeValid_prime [2, 11, 13, 41] ⟨93809, 3, [(2, 4), (11, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_95789 : Nat.Prime 95789 := by
  apply nodeValid_prime [2, 7, 11, 311] ⟨95789, 2, [(2, 2), (7, 1), (11, 1), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_311
  · decide +kernel

theorem prime_120899 : Nat.Prime 120899 := by
  apply nodeValid_prime [2, 60449] ⟨120899, 2, [(2, 1), (60449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60449
  · decide +kernel

theorem prime_152077 : Nat.Prime 152077 := by
  apply nodeValid_prime [2, 3, 19, 23, 29] ⟨152077, 6, [(2, 2), (3, 1), (19, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_152147 : Nat.Prime 152147 := by
  apply nodeValid_prime [2, 127, 599] ⟨152147, 2, [(2, 1), (127, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_599
  · decide +kernel

theorem prime_154313 : Nat.Prime 154313 := by
  apply nodeValid_prime [2, 19289] ⟨154313, 3, [(2, 3), (19289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19289
  · decide +kernel

theorem prime_159899 : Nat.Prime 159899 := by
  apply nodeValid_prime [2, 31, 2579] ⟨159899, 2, [(2, 1), (31, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2579
  · decide +kernel

theorem prime_182929 : Nat.Prime 182929 := by
  apply nodeValid_prime [2, 3, 37, 103] ⟨182929, 7, [(2, 4), (3, 1), (37, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_103
  · decide +kernel

theorem prime_191579 : Nat.Prime 191579 := by
  apply nodeValid_prime [2, 95789] ⟨191579, 2, [(2, 1), (95789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_95789
  · decide +kernel

theorem prime_213067 : Nat.Prime 213067 := by
  apply nodeValid_prime [2, 3, 7, 19, 89] ⟨213067, 2, [(2, 1), (3, 2), (7, 1), (19, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_89
  · decide +kernel

theorem prime_214147 : Nat.Prime 214147 := by
  apply nodeValid_prime [2, 3, 11897] ⟨214147, 2, [(2, 1), (3, 2), (11897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11897
  · decide +kernel

theorem prime_248981 : Nat.Prime 248981 := by
  apply nodeValid_prime [2, 5, 59, 211] ⟨248981, 2, [(2, 2), (5, 1), (59, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_211
  · decide +kernel

theorem prime_320063 : Nat.Prime 320063 := by
  apply nodeValid_prime [2, 160031] ⟨320063, 5, [(2, 1), (160031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160031
  · decide +kernel

theorem prime_323077 : Nat.Prime 323077 := by
  apply nodeValid_prime [2, 3, 13, 19, 109] ⟨323077, 5, [(2, 2), (3, 1), (13, 1), (19, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_109
  · decide +kernel

theorem prime_341087 : Nat.Prime 341087 := by
  apply nodeValid_prime [2, 199, 857] ⟨341087, 5, [(2, 1), (199, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_857
  · decide +kernel

theorem prime_421093 : Nat.Prime 421093 := by
  apply nodeValid_prime [2, 3, 7, 557] ⟨421093, 2, [(2, 2), (3, 3), (7, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_557
  · decide +kernel

theorem prime_497963 : Nat.Prime 497963 := by
  apply nodeValid_prime [2, 248981] ⟨497963, 2, [(2, 1), (248981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_248981
  · decide +kernel

theorem prime_560221 : Nat.Prime 560221 := by
  apply nodeValid_prime [2, 3, 5, 9337] ⟨560221, 2, [(2, 2), (3, 1), (5, 1), (9337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9337
  · decide +kernel

theorem prime_576221 : Nat.Prime 576221 := by
  apply nodeValid_prime [2, 5, 47, 613] ⟨576221, 2, [(2, 2), (5, 1), (47, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_613
  · decide +kernel

theorem prime_623683 : Nat.Prime 623683 := by
  apply nodeValid_prime [2, 3, 34649] ⟨623683, 2, [(2, 1), (3, 2), (34649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34649
  · decide +kernel

theorem prime_659657 : Nat.Prime 659657 := by
  apply nodeValid_prime [2, 82457] ⟨659657, 3, [(2, 3), (82457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_82457
  · decide +kernel

theorem prime_795737 : Nat.Prime 795737 := by
  apply nodeValid_prime [2, 17, 5851] ⟨795737, 3, [(2, 3), (17, 1), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_5851
  · decide +kernel

theorem prime_1195123 : Nat.Prime 1195123 := by
  apply nodeValid_prime [2, 3, 139, 1433] ⟨1195123, 2, [(2, 1), (3, 1), (139, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_1433
  · decide +kernel

theorem prime_1288709 : Nat.Prime 1288709 := by
  apply nodeValid_prime [2, 107, 3011] ⟨1288709, 2, [(2, 2), (107, 1), (3011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_3011
  · decide +kernel

theorem prime_1292309 : Nat.Prime 1292309 := by
  apply nodeValid_prime [2, 323077] ⟨1292309, 2, [(2, 2), (323077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_323077
  · decide +kernel

theorem prime_1891753 : Nat.Prime 1891753 := by
  apply nodeValid_prime [2, 3, 78823] ⟨1891753, 5, [(2, 3), (3, 1), (78823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_78823
  · decide +kernel

theorem prime_1963259 : Nat.Prime 1963259 := by
  apply nodeValid_prime [2, 11, 233, 383] ⟨1963259, 2, [(2, 1), (11, 1), (233, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_233
    · exact prime_383
  · decide +kernel

theorem prime_2541157 : Nat.Prime 2541157 := by
  apply nodeValid_prime [2, 3, 421, 503] ⟨2541157, 2, [(2, 2), (3, 1), (421, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_421
    · exact prime_503
  · decide +kernel

theorem prime_2584619 : Nat.Prime 2584619 := by
  apply nodeValid_prime [2, 1292309] ⟨2584619, 2, [(2, 1), (1292309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1292309
  · decide +kernel

theorem prime_2663429 : Nat.Prime 2663429 := by
  apply nodeValid_prime [2, 665857] ⟨2663429, 2, [(2, 2), (665857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_665857
  · decide +kernel

theorem prime_2700829 : Nat.Prime 2700829 := by
  apply nodeValid_prime [2, 3, 13, 29, 199] ⟨2700829, 2, [(2, 2), (3, 2), (13, 1), (29, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_199
  · decide +kernel

theorem prime_2775889 : Nat.Prime 2775889 := by
  apply nodeValid_prime [2, 3, 37, 521] ⟨2775889, 11, [(2, 4), (3, 2), (37, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_521
  · decide +kernel

theorem prime_3210289 : Nat.Prime 3210289 := by
  apply nodeValid_prime [2, 3, 47, 1423] ⟨3210289, 7, [(2, 4), (3, 1), (47, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_1423
  · decide +kernel

theorem prime_3383581 : Nat.Prime 3383581 := by
  apply nodeValid_prime [2, 3, 5, 56393] ⟨3383581, 10, [(2, 2), (3, 1), (5, 1), (56393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_56393
  · decide +kernel

theorem prime_4253273 : Nat.Prime 4253273 := by
  apply nodeValid_prime [2, 73, 7283] ⟨4253273, 3, [(2, 3), (73, 1), (7283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_7283
  · decide +kernel

theorem prime_4556813 : Nat.Prime 4556813 := by
  apply nodeValid_prime [2, 13, 87631] ⟨4556813, 2, [(2, 2), (13, 1), (87631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_87631
  · decide +kernel

theorem prime_4606997 : Nat.Prime 4606997 := by
  apply nodeValid_prime [2, 89, 12941] ⟨4606997, 2, [(2, 2), (89, 1), (12941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_12941
  · decide +kernel

theorem prime_4844527 : Nat.Prime 4844527 := by
  apply nodeValid_prime [2, 3, 761, 1061] ⟨4844527, 3, [(2, 1), (3, 1), (761, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_761
    · exact prime_1061
  · decide +kernel

theorem prime_5037731 : Nat.Prime 5037731 := by
  apply nodeValid_prime [2, 5, 67, 73, 103] ⟨5037731, 2, [(2, 1), (5, 1), (67, 1), (73, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_73
    · exact prime_103
  · decide +kernel

theorem prime_6260381 : Nat.Prime 6260381 := by
  apply nodeValid_prime [2, 5, 7, 97, 461] ⟨6260381, 2, [(2, 2), (5, 1), (7, 1), (97, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_97
    · exact prime_461
  · decide +kernel

theorem prime_7170739 : Nat.Prime 7170739 := by
  apply nodeValid_prime [2, 3, 1195123] ⟨7170739, 2, [(2, 1), (3, 1), (1195123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1195123
  · decide +kernel

theorem prime_7694663 : Nat.Prime 7694663 := by
  apply nodeValid_prime [2, 59, 61, 1069] ⟨7694663, 5, [(2, 1), (59, 1), (61, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_61
    · exact prime_1069
  · decide +kernel

theorem prime_10155517 : Nat.Prime 10155517 := by
  apply nodeValid_prime [2, 3, 7, 120899] ⟨10155517, 2, [(2, 2), (3, 1), (7, 1), (120899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_120899
  · decide +kernel

theorem prime_10651733 : Nat.Prime 10651733 := by
  apply nodeValid_prime [2, 7, 13, 2251] ⟨10651733, 2, [(2, 2), (7, 1), (13, 2), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_2251
  · decide +kernel

theorem prime_17430911 : Nat.Prime 17430911 := by
  apply nodeValid_prime [2, 5, 7, 43, 5791] ⟨17430911, 11, [(2, 1), (5, 1), (7, 1), (43, 1), (5791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_5791
  · decide +kernel

theorem prime_18156967 : Nat.Prime 18156967 := by
  apply nodeValid_prime [2, 3, 641, 4721] ⟨18156967, 3, [(2, 1), (3, 1), (641, 1), (4721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_641
    · exact prime_4721
  · decide +kernel

theorem prime_19004119 : Nat.Prime 19004119 := by
  apply nodeValid_prime [2, 3, 7, 23, 103, 191] ⟨19004119, 6, [(2, 1), (3, 1), (7, 1), (23, 1), (103, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_103
    · exact prime_191
  · decide +kernel

theorem prime_21303467 : Nat.Prime 21303467 := by
  apply nodeValid_prime [2, 10651733] ⟨21303467, 2, [(2, 1), (10651733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10651733
  · decide +kernel

theorem prime_27426023 : Nat.Prime 27426023 := by
  apply nodeValid_prime [2, 13, 71, 83, 179] ⟨27426023, 5, [(2, 1), (13, 1), (71, 1), (83, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71
    · exact prime_83
    · exact prime_179
  · decide +kernel

theorem prime_30244657 : Nat.Prime 30244657 := by
  apply nodeValid_prime [2, 3, 13, 19, 2551] ⟨30244657, 5, [(2, 4), (3, 1), (13, 1), (19, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_2551
  · decide +kernel

theorem prime_32102891 : Nat.Prime 32102891 := by
  apply nodeValid_prime [2, 5, 3210289] ⟨32102891, 2, [(2, 1), (5, 1), (3210289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3210289
  · decide +kernel

theorem prime_32218421 : Nat.Prime 32218421 := by
  apply nodeValid_prime [2, 5, 13, 29, 4273] ⟨32218421, 3, [(2, 2), (5, 1), (13, 1), (29, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
    · exact prime_4273
  · decide +kernel

theorem prime_33606901 : Nat.Prime 33606901 := by
  apply nodeValid_prime [2, 3, 5, 461] ⟨33606901, 2, [(2, 2), (3, 6), (5, 2), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_461
  · decide +kernel

theorem prime_50083049 : Nat.Prime 50083049 := by
  apply nodeValid_prime [2, 6260381] ⟨50083049, 3, [(2, 3), (6260381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6260381
  · decide +kernel

theorem prime_58397723 : Nat.Prime 58397723 := by
  apply nodeValid_prime [2, 113, 233, 1109] ⟨58397723, 2, [(2, 1), (113, 1), (233, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_233
    · exact prime_1109
  · decide +kernel

theorem prime_64854347 : Nat.Prime 64854347 := by
  apply nodeValid_prime [2, 61, 109, 4877] ⟨64854347, 2, [(2, 1), (61, 1), (109, 1), (4877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_109
    · exact prime_4877
  · decide +kernel

theorem prime_104204939 : Nat.Prime 104204939 := by
  apply nodeValid_prime [2, 89, 149, 3929] ⟨104204939, 2, [(2, 1), (89, 1), (149, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_149
    · exact prime_3929
  · decide +kernel

theorem prime_116795447 : Nat.Prime 116795447 := by
  apply nodeValid_prime [2, 58397723] ⟨116795447, 5, [(2, 1), (58397723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58397723
  · decide +kernel

theorem prime_127965743 : Nat.Prime 127965743 := by
  apply nodeValid_prime [2, 1613, 39667] ⟨127965743, 5, [(2, 1), (1613, 1), (39667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1613
    · exact prime_39667
  · decide +kernel

theorem prime_133126381 : Nat.Prime 133126381 := by
  apply nodeValid_prime [2, 3, 5, 857, 863] ⟨133126381, 10, [(2, 2), (3, 2), (5, 1), (857, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_857
    · exact prime_863
  · decide +kernel

theorem prime_195258473 : Nat.Prime 195258473 := by
  apply nodeValid_prime [2, 37, 659657] ⟨195258473, 3, [(2, 3), (37, 1), (659657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_659657
  · decide +kernel

theorem prime_216139907 : Nat.Prime 216139907 := by
  apply nodeValid_prime [2, 2549, 42397] ⟨216139907, 2, [(2, 1), (2549, 1), (42397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2549
    · exact prime_42397
  · decide +kernel

theorem prime_354021137 : Nat.Prime 354021137 := by
  apply nodeValid_prime [2, 7, 127, 24889] ⟨354021137, 3, [(2, 4), (7, 1), (127, 1), (24889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_127
    · exact prime_24889
  · decide +kernel

theorem prime_413658691 : Nat.Prime 413658691 := by
  apply nodeValid_prime [2, 3, 5, 19, 61, 11897] ⟨413658691, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (11897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_61
    · exact prime_11897
  · decide +kernel

theorem prime_425676577 : Nat.Prime 425676577 := by
  apply nodeValid_prime [2, 3, 13, 341087] ⟨425676577, 5, [(2, 5), (3, 1), (13, 1), (341087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_341087
  · decide +kernel

theorem prime_438886697 : Nat.Prime 438886697 := by
  apply nodeValid_prime [2, 29, 1891753] ⟨438886697, 3, [(2, 3), (29, 1), (1891753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1891753
  · decide +kernel

theorem prime_585319271 : Nat.Prime 585319271 := by
  apply nodeValid_prime [2, 5, 139, 421093] ⟨585319271, 11, [(2, 1), (5, 1), (139, 1), (421093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_421093
  · decide +kernel

theorem prime_699154639 : Nat.Prime 699154639 := by
  apply nodeValid_prime [2, 3, 7, 13, 182929] ⟨699154639, 3, [(2, 1), (3, 1), (7, 2), (13, 1), (182929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_182929
  · decide +kernel

theorem prime_1030989473 : Nat.Prime 1030989473 := by
  apply nodeValid_prime [2, 32218421] ⟨1030989473, 3, [(2, 5), (32218421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32218421
  · decide +kernel

theorem prime_2146433539 : Nat.Prime 2146433539 := by
  apply nodeValid_prime [2, 3, 53, 571, 11821] ⟨2146433539, 2, [(2, 1), (3, 1), (53, 1), (571, 1), (11821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_571
    · exact prime_11821
  · decide +kernel

theorem prime_2533979887 : Nat.Prime 2533979887 := by
  apply nodeValid_prime [2, 3, 4483, 94207] ⟨2533979887, 3, [(2, 1), (3, 1), (4483, 1), (94207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4483
    · exact prime_94207
  · decide +kernel

theorem prime_2554059463 : Nat.Prime 2554059463 := by
  apply nodeValid_prime [2, 3, 425676577] ⟨2554059463, 3, [(2, 1), (3, 1), (425676577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_425676577
  · decide +kernel

theorem prime_2796618557 : Nat.Prime 2796618557 := by
  apply nodeValid_prime [2, 699154639] ⟨2796618557, 2, [(2, 2), (699154639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_699154639
  · decide +kernel

theorem prime_2817629527 : Nat.Prime 2817629527 := by
  apply nodeValid_prime [2, 3, 21227, 22123] ⟨2817629527, 3, [(2, 1), (3, 1), (21227, 1), (22123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21227
    · exact prime_22123
  · decide +kernel

theorem prime_2832169097 : Nat.Prime 2832169097 := by
  apply nodeValid_prime [2, 354021137] ⟨2832169097, 3, [(2, 3), (354021137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_354021137
  · decide +kernel

theorem prime_3062940449 : Nat.Prime 3062940449 := by
  apply nodeValid_prime [2, 19, 5037731] ⟨3062940449, 3, [(2, 5), (19, 1), (5037731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5037731
  · decide +kernel

theorem prime_6813285067 : Nat.Prime 6813285067 := by
  apply nodeValid_prime [2, 3, 7, 431, 17923] ⟨6813285067, 7, [(2, 1), (3, 2), (7, 2), (431, 1), (17923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_431
    · exact prime_17923
  · decide +kernel

theorem prime_8591372813 : Nat.Prime 8591372813 := by
  apply nodeValid_prime [2, 11, 195258473] ⟨8591372813, 2, [(2, 2), (11, 1), (195258473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_195258473
  · decide +kernel

theorem prime_10114168651 : Nat.Prime 10114168651 := by
  apply nodeValid_prime [2, 3, 5, 827, 81533] ⟨10114168651, 2, [(2, 1), (3, 1), (5, 2), (827, 1), (81533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_827
    · exact prime_81533
  · decide +kernel

theorem prime_11715121529 : Nat.Prime 11715121529 := by
  apply nodeValid_prime [2, 11, 133126381] ⟨11715121529, 6, [(2, 3), (11, 1), (133126381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_133126381
  · decide +kernel

theorem prime_14094010163 : Nat.Prime 14094010163 := by
  apply nodeValid_prime [2, 233, 30244657] ⟨14094010163, 2, [(2, 1), (233, 1), (30244657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_30244657
  · decide +kernel

theorem prime_15324356779 : Nat.Prime 15324356779 := by
  apply nodeValid_prime [2, 3, 2554059463] ⟨15324356779, 3, [(2, 1), (3, 1), (2554059463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2554059463
  · decide +kernel

theorem prime_16779711343 : Nat.Prime 16779711343 := by
  apply nodeValid_prime [2, 3, 2796618557] ⟨16779711343, 5, [(2, 1), (3, 1), (2796618557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2796618557
  · decide +kernel

theorem prime_35480816573 : Nat.Prime 35480816573 := by
  apply nodeValid_prime [2, 1237, 7170739] ⟨35480816573, 2, [(2, 2), (1237, 1), (7170739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1237
    · exact prime_7170739
  · decide +kernel

theorem prime_42881166287 : Nat.Prime 42881166287 := by
  apply nodeValid_prime [2, 7, 3062940449] ⟨42881166287, 5, [(2, 1), (7, 1), (3062940449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3062940449
  · decide +kernel

theorem prime_50299124713 : Nat.Prime 50299124713 := by
  apply nodeValid_prime [2, 3, 33923, 61781] ⟨50299124713, 7, [(2, 3), (3, 1), (33923, 1), (61781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33923
    · exact prime_61781
  · decide +kernel

theorem prime_63490800977 : Nat.Prime 63490800977 := by
  apply nodeValid_prime [2, 19, 223, 347, 2699] ⟨63490800977, 3, [(2, 4), (19, 1), (223, 1), (347, 1), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_223
    · exact prime_347
    · exact prime_2699
  · decide +kernel

theorem prime_112307820553 : Nat.Prime 112307820553 := by
  apply nodeValid_prime [2, 3, 461, 3383581] ⟨112307820553, 5, [(2, 3), (3, 2), (461, 1), (3383581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
    · exact prime_3383581
  · decide +kernel

theorem prime_158226895847 : Nat.Prime 158226895847 := by
  apply nodeValid_prime [2, 59, 683, 1963259] ⟨158226895847, 5, [(2, 1), (59, 1), (683, 1), (1963259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_683
    · exact prime_1963259
  · decide +kernel

theorem prime_169528815217 : Nat.Prime 169528815217 := by
  apply nodeValid_prime [2, 3, 17, 7694663] ⟨169528815217, 5, [(2, 4), (3, 4), (17, 1), (7694663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_7694663
  · decide +kernel

theorem prime_169930145821 : Nat.Prime 169930145821 := by
  apply nodeValid_prime [2, 3, 5, 2832169097] ⟨169930145821, 6, [(2, 2), (3, 1), (5, 1), (2832169097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2832169097
  · decide +kernel

theorem prime_260192655347 : Nat.Prime 260192655347 := by
  apply nodeValid_prime [2, 13, 31267, 320063] ⟨260192655347, 2, [(2, 1), (13, 1), (31267, 1), (320063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31267
    · exact prime_320063
  · decide +kernel

theorem prime_292948609391 : Nat.Prime 292948609391 := by
  apply nodeValid_prime [2, 5, 179, 3217, 50873] ⟨292948609391, 14, [(2, 1), (5, 1), (179, 1), (3217, 1), (50873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
    · exact prime_3217
    · exact prime_50873
  · decide +kernel

theorem prime_336391345109 : Nat.Prime 336391345109 := by
  apply nodeValid_prime [2, 7, 13, 10155517] ⟨336391345109, 2, [(2, 2), (7, 2), (13, 2), (10155517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_10155517
  · decide +kernel

theorem prime_393698838121 : Nat.Prime 393698838121 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 31, 795737] ⟨393698838121, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (19, 1), (31, 1), (795737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_31
    · exact prime_795737
  · decide +kernel

theorem prime_395255420309 : Nat.Prime 395255420309 := by
  apply nodeValid_prime [2, 7, 29, 59, 127, 167, 389] ⟨395255420309, 2, [(2, 2), (7, 1), (29, 1), (59, 1), (127, 1), (167, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_59
    · exact prime_127
    · exact prime_167
    · exact prime_389
  · decide +kernel

theorem prime_782433901253 : Nat.Prime 782433901253 := by
  apply nodeValid_prime [2, 37, 191, 4591, 6029] ⟨782433901253, 2, [(2, 2), (37, 1), (191, 1), (4591, 1), (6029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_191
    · exact prime_4591
    · exact prime_6029
  · decide +kernel

theorem prime_785533764971 : Nat.Prime 785533764971 := by
  apply nodeValid_prime [2, 5, 31, 2533979887] ⟨785533764971, 2, [(2, 1), (5, 1), (31, 1), (2533979887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_2533979887
  · decide +kernel

theorem prime_2343588875129 : Nat.Prime 2343588875129 := by
  apply nodeValid_prime [2, 292948609391] ⟨2343588875129, 3, [(2, 3), (292948609391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_292948609391
  · decide +kernel

theorem prime_2345444767013 : Nat.Prime 2345444767013 := by
  apply nodeValid_prime [2, 17, 331, 104204939] ⟨2345444767013, 2, [(2, 2), (17, 1), (331, 1), (104204939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_331
    · exact prime_104204939
  · decide +kernel

theorem prime_2377148195969 : Nat.Prime 2377148195969 := by
  apply nodeValid_prime [2, 7, 13, 953, 214147] ⟨2377148195969, 3, [(2, 7), (7, 1), (13, 1), (953, 1), (214147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_953
    · exact prime_214147
  · decide +kernel

theorem prime_4679759910619 : Nat.Prime 4679759910619 := by
  apply nodeValid_prime [2, 3, 13, 1447, 4606997] ⟨4679759910619, 2, [(2, 1), (3, 3), (13, 1), (1447, 1), (4606997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1447
    · exact prime_4606997
  · decide +kernel

theorem prime_4679759970397 : Nat.Prime 4679759970397 := by
  apply nodeValid_prime [2, 3, 7, 53, 116795447] ⟨4679759970397, 5, [(2, 2), (3, 3), (7, 1), (53, 1), (116795447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_116795447
  · decide +kernel

theorem prime_4679759970827 : Nat.Prime 4679759970827 := by
  apply nodeValid_prime [2, 109, 331, 64854347] ⟨4679759970827, 2, [(2, 1), (109, 1), (331, 1), (64854347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_331
    · exact prime_64854347
  · decide +kernel

theorem prime_4683467787637 : Nat.Prime 4683467787637 := by
  apply nodeValid_prime [2, 3, 11, 35480816573] ⟨4683467787637, 2, [(2, 2), (3, 1), (11, 1), (35480816573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_35480816573
  · decide +kernel

theorem prime_4683467796131 : Nat.Prime 4683467796131 := by
  apply nodeValid_prime [2, 5, 1201, 4157, 93809] ⟨4683467796131, 2, [(2, 1), (5, 1), (1201, 1), (4157, 1), (93809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1201
    · exact prime_4157
    · exact prime_93809
  · decide +kernel

theorem prime_4683467796247 : Nat.Prime 4683467796247 := by
  apply nodeValid_prime [2, 3, 260192655347] ⟨4683467796247, 3, [(2, 1), (3, 2), (260192655347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_260192655347
  · decide +kernel

theorem prime_4687177660673 : Nat.Prime 4687177660673 := by
  apply nodeValid_prime [2, 13, 19, 877, 84523] ⟨4687177660673, 3, [(2, 8), (13, 1), (19, 1), (877, 1), (84523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_877
    · exact prime_84523
  · decide +kernel

theorem prime_4687177749493 : Nat.Prime 4687177749493 := by
  apply nodeValid_prime [2, 3, 7, 29, 37, 337, 154313] ⟨4687177749493, 2, [(2, 2), (3, 1), (7, 1), (29, 1), (37, 1), (337, 1), (154313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_37
    · exact prime_337
    · exact prime_154313
  · decide +kernel

theorem prime_4687177750259 : Nat.Prime 4687177750259 := by
  apply nodeValid_prime [2, 2343588875129] ⟨4687177750259, 2, [(2, 1), (2343588875129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2343588875129
  · decide +kernel

theorem prime_4690889534027 : Nat.Prime 4690889534027 := by
  apply nodeValid_prime [2, 2345444767013] ⟨4690889534027, 2, [(2, 1), (2345444767013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2345444767013
  · decide +kernel

theorem prime_4690889555899 : Nat.Prime 4690889555899 := by
  apply nodeValid_prime [2, 3, 7, 13, 8591372813] ⟨4690889555899, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (8591372813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_8591372813
  · decide +kernel

theorem prime_4690889555941 : Nat.Prime 4690889555941 := by
  apply nodeValid_prime [2, 3, 5, 7, 413658691] ⟨4690889555941, 6, [(2, 2), (3, 4), (5, 1), (7, 1), (413658691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_413658691
  · decide +kernel

theorem prime_4694603407519 : Nat.Prime 4694603407519 := by
  apply nodeValid_prime [2, 3, 782433901253] ⟨4694603407519, 3, [(2, 1), (3, 1), (782433901253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_782433901253
  · decide +kernel

theorem prime_4694603428129 : Nat.Prime 4694603428129 := by
  apply nodeValid_prime [2, 3, 29, 151, 2689, 4153] ⟨4694603428129, 7, [(2, 5), (3, 1), (29, 1), (151, 1), (2689, 1), (4153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_151
    · exact prime_2689
    · exact prime_4153
  · decide +kernel

theorem prime_4698319175141 : Nat.Prime 4698319175141 := by
  apply nodeValid_prime [2, 5, 48491, 4844527] ⟨4698319175141, 3, [(2, 2), (5, 1), (48491, 1), (4844527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_48491
    · exact prime_4844527
  · decide +kernel

theorem prime_4698319176041 : Nat.Prime 4698319176041 := by
  apply nodeValid_prime [2, 5, 7, 16779711343] ⟨4698319176041, 3, [(2, 3), (5, 1), (7, 1), (16779711343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_16779711343
  · decide +kernel

theorem prime_4698319272299 : Nat.Prime 4698319272299 := by
  apply nodeValid_prime [2, 37, 63490800977] ⟨4698319272299, 2, [(2, 1), (37, 1), (63490800977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_63490800977
  · decide +kernel

theorem prime_4702037116123 : Nat.Prime 4702037116123 := by
  apply nodeValid_prime [2, 3, 14387, 18156967] ⟨4702037116123, 5, [(2, 1), (3, 2), (14387, 1), (18156967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14387
    · exact prime_18156967
  · decide +kernel

theorem prime_4702037116289 : Nat.Prime 4702037116289 := by
  apply nodeValid_prime [2, 37, 1723, 576221] ⟨4702037116289, 3, [(2, 7), (37, 1), (1723, 1), (576221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1723
    · exact prime_576221
  · decide +kernel

theorem prime_4702037131219 : Nat.Prime 4702037131219 := by
  apply nodeValid_prime [2, 3, 7, 43, 137, 19004119] ⟨4702037131219, 10, [(2, 1), (3, 1), (7, 1), (43, 1), (137, 1), (19004119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_137
    · exact prime_19004119
  · decide +kernel

theorem prime_4705756989719 : Nat.Prime 4705756989719 := by
  apply nodeValid_prime [2, 83, 6221, 4556813] ⟨4705756989719, 7, [(2, 1), (83, 1), (6221, 1), (4556813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_6221
    · exact prime_4556813
  · decide +kernel

theorem prime_4705756997353 : Nat.Prime 4705756997353 := by
  apply nodeValid_prime [2, 3, 152147, 1288709] ⟨4705756997353, 7, [(2, 3), (3, 1), (152147, 1), (1288709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152147
    · exact prime_1288709
  · decide +kernel

theorem prime_4705756998203 : Nat.Prime 4705756998203 := by
  apply nodeValid_prime [2, 13, 19, 3527, 2700829] ⟨4705756998203, 2, [(2, 1), (13, 1), (19, 1), (3527, 1), (2700829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_3527
    · exact prime_2700829
  · decide +kernel

theorem prime_4709478831527 : Nat.Prime 4709478831527 := by
  apply nodeValid_prime [2, 7, 336391345109] ⟨4709478831527, 7, [(2, 1), (7, 1), (336391345109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_336391345109
  · decide +kernel

theorem prime_4709478854467 : Nat.Prime 4709478854467 := by
  apply nodeValid_prime [2, 3, 149, 585319271] ⟨4709478854467, 2, [(2, 1), (3, 3), (149, 1), (585319271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_585319271
  · decide +kernel

theorem prime_4709478854659 : Nat.Prime 4709478854659 := by
  apply nodeValid_prime [2, 3, 67, 11715121529] ⟨4709478854659, 2, [(2, 1), (3, 1), (67, 1), (11715121529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_11715121529
  · decide +kernel

theorem prime_4713202589827 : Nat.Prime 4713202589827 := by
  apply nodeValid_prime [2, 3, 785533764971] ⟨4713202589827, 2, [(2, 1), (3, 1), (785533764971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_785533764971
  · decide +kernel

theorem prime_4713202591367 : Nat.Prime 4713202591367 := by
  apply nodeValid_prime [2, 233, 10114168651] ⟨4713202591367, 5, [(2, 1), (233, 1), (10114168651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_10114168651
  · decide +kernel

theorem prime_4713202654403 : Nat.Prime 4713202654403 := by
  apply nodeValid_prime [2, 11, 82889, 2584619] ⟨4713202654403, 2, [(2, 1), (11, 1), (82889, 1), (2584619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_82889
    · exact prime_2584619
  · decide +kernel

theorem prime_4716928289921 : Nat.Prime 4716928289921 := by
  apply nodeValid_prime [2, 5, 7, 11, 19, 5037731] ⟨4716928289921, 3, [(2, 7), (5, 1), (7, 1), (11, 1), (19, 1), (5037731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_5037731
  · decide +kernel

theorem prime_4716928291571 : Nat.Prime 4716928291571 := by
  apply nodeValid_prime [2, 5, 11, 42881166287] ⟨4716928291571, 6, [(2, 1), (5, 1), (11, 1), (42881166287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_42881166287
  · decide +kernel

theorem prime_4716928463227 : Nat.Prime 4716928463227 := by
  apply nodeValid_prime [2, 3, 7, 112307820553] ⟨4716928463227, 2, [(2, 1), (3, 1), (7, 1), (112307820553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_112307820553
  · decide +kernel

theorem prime_4720656259271 : Nat.Prime 4720656259271 := by
  apply nodeValid_prime [2, 5, 7, 17, 31, 127965743] ⟨4720656259271, 14, [(2, 1), (5, 1), (7, 1), (17, 1), (31, 1), (127965743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_127965743
  · decide +kernel

theorem prime_4720656374443 : Nat.Prime 4720656374443 := by
  apply nodeValid_prime [2, 3, 283, 1861, 497963] ⟨4720656374443, 2, [(2, 1), (3, 2), (283, 1), (1861, 1), (497963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1861
    · exact prime_497963
  · decide +kernel

theorem prime_4720656374779 : Nat.Prime 4720656374779 := by
  apply nodeValid_prime [2, 3, 179, 22943, 191579] ⟨4720656374779, 3, [(2, 1), (3, 1), (179, 1), (22943, 1), (191579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_22943
    · exact prime_191579
  · decide +kernel

theorem prime_4724386057453 : Nat.Prime 4724386057453 := by
  apply nodeValid_prime [2, 3, 393698838121] ⟨4724386057453, 2, [(2, 2), (3, 1), (393698838121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_393698838121
  · decide +kernel

theorem prime_4724386087207 : Nat.Prime 4724386087207 := by
  apply nodeValid_prime [2, 3, 3643, 216139907] ⟨4724386087207, 3, [(2, 1), (3, 1), (3643, 1), (216139907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3643
    · exact prime_216139907
  · decide +kernel

theorem prime_4724386087537 : Nat.Prime 4724386087537 := by
  apply nodeValid_prime [2, 3, 19, 10799, 159899] ⟨4724386087537, 10, [(2, 4), (3, 2), (19, 1), (10799, 1), (159899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_10799
    · exact prime_159899
  · decide +kernel

theorem prime_4728117723023 : Nat.Prime 4728117723023 := by
  apply nodeValid_prime [2, 47, 50299124713] ⟨4728117723023, 5, [(2, 1), (47, 1), (50299124713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_50299124713
  · decide +kernel

theorem prime_4728117723179 : Nat.Prime 4728117723179 := by
  apply nodeValid_prime [2, 2293, 1030989473] ⟨4728117723179, 2, [(2, 1), (2293, 1), (1030989473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2293
    · exact prime_1030989473
  · decide +kernel

theorem prime_4728117861611 : Nat.Prime 4728117861611 := by
  apply nodeValid_prime [2, 5, 11, 13, 401, 1549, 5323] ⟨4728117861611, 2, [(2, 1), (5, 1), (11, 1), (13, 1), (401, 1), (1549, 1), (5323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_401
    · exact prime_1549
    · exact prime_5323
  · decide +kernel

theorem prime_4731851660801 : Nat.Prime 4731851660801 := by
  apply nodeValid_prime [2, 5, 11, 33606901] ⟨4731851660801, 3, [(2, 9), (5, 2), (11, 1), (33606901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_33606901
  · decide +kernel

theorem prime_4731851736851 : Nat.Prime 4731851736851 := by
  apply nodeValid_prime [2, 5, 7, 53, 409, 623683] ⟨4731851736851, 2, [(2, 1), (5, 2), (7, 1), (53, 1), (409, 1), (623683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_409
    · exact prime_623683
  · decide +kernel

theorem prime_4731851737531 : Nat.Prime 4731851737531 := by
  apply nodeValid_prime [2, 3, 5, 31, 131, 317, 40841] ⟨4731851737531, 2, [(2, 1), (3, 2), (5, 1), (31, 1), (131, 1), (317, 1), (40841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_131
    · exact prime_317
    · exact prime_40841
  · decide +kernel

theorem prime_4735587414769 : Nat.Prime 4735587414769 := by
  apply nodeValid_prime [2, 3, 7, 14094010163] ⟨4735587414769, 11, [(2, 4), (3, 1), (7, 1), (14094010163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14094010163
  · decide +kernel

theorem prime_4735587415717 : Nat.Prime 4735587415717 := by
  apply nodeValid_prime [2, 3, 101, 163, 2663429] ⟨4735587415717, 2, [(2, 2), (3, 3), (101, 1), (163, 1), (2663429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_163
    · exact prime_2663429
  · decide +kernel

theorem prime_4735587460631 : Nat.Prime 4735587460631 := by
  apply nodeValid_prime [2, 5, 13, 83, 438886697] ⟨4735587460631, 11, [(2, 1), (5, 1), (13, 1), (83, 1), (438886697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_83
    · exact prime_438886697
  · decide +kernel

theorem prime_4739325253613 : Nat.Prime 4739325253613 := by
  apply nodeValid_prime [2, 101, 673, 17430911] ⟨4739325253613, 2, [(2, 2), (101, 1), (673, 1), (17430911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_673
    · exact prime_17430911
  · decide +kernel

theorem prime_4739325254113 : Nat.Prime 4739325254113 := by
  apply nodeValid_prime [2, 3, 23, 2146433539] ⟨4739325254113, 5, [(2, 5), (3, 1), (23, 1), (2146433539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2146433539
  · decide +kernel

theorem prime_4739325255703 : Nat.Prime 4739325255703 := by
  apply nodeValid_prime [2, 3, 1171, 2775889] ⟨4739325255703, 3, [(2, 1), (3, 6), (1171, 1), (2775889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1171
    · exact prime_2775889
  · decide +kernel

theorem prime_4743065043709 : Nat.Prime 4743065043709 := by
  apply nodeValid_prime [2, 3, 395255420309] ⟨4743065043709, 6, [(2, 2), (3, 1), (395255420309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_395255420309
  · decide +kernel

theorem prime_4743065072353 : Nat.Prime 4743065072353 := by
  apply nodeValid_prime [2, 3, 19, 17099, 152077] ⟨4743065072353, 5, [(2, 5), (3, 1), (19, 1), (17099, 1), (152077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_17099
    · exact prime_152077
  · decide +kernel

theorem prime_4743065072497 : Nat.Prime 4743065072497 := by
  apply nodeValid_prime [2, 3, 1973, 50083049] ⟨4743065072497, 5, [(2, 4), (3, 1), (1973, 1), (50083049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1973
    · exact prime_50083049
  · decide +kernel

theorem prime_4746806826077 : Nat.Prime 4746806826077 := by
  apply nodeValid_prime [2, 7, 169528815217] ⟨4746806826077, 2, [(2, 2), (7, 1), (169528815217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_169528815217
  · decide +kernel

theorem prime_4746806874499 : Nat.Prime 4746806874499 := by
  apply nodeValid_prime [2, 3, 13, 17, 109, 173, 859] ⟨4746806874499, 2, [(2, 1), (3, 1), (13, 2), (17, 2), (109, 1), (173, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_109
    · exact prime_173
    · exact prime_859
  · decide +kernel

theorem prime_4746806875411 : Nat.Prime 4746806875411 := by
  apply nodeValid_prime [2, 3, 5, 158226895847] ⟨4746806875411, 2, [(2, 1), (3, 1), (5, 1), (158226895847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_158226895847
  · decide +kernel

theorem prime_4750550601491 : Nat.Prime 4750550601491 := by
  apply nodeValid_prime [2, 5, 31, 15324356779] ⟨4750550601491, 2, [(2, 1), (5, 1), (31, 1), (15324356779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_15324356779
  · decide +kernel

theorem prime_4750550641801 : Nat.Prime 4750550641801 := by
  apply nodeValid_prime [2, 3, 5, 17, 5879, 26407] ⟨4750550641801, 14, [(2, 3), (3, 2), (5, 2), (17, 1), (5879, 1), (26407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_5879
    · exact prime_26407
  · decide +kernel

theorem prime_4754296372127 : Nat.Prime 4754296372127 := by
  apply nodeValid_prime [2, 7, 17, 1123, 2541157] ⟨4754296372127, 7, [(2, 1), (7, 2), (17, 1), (1123, 1), (2541157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1123
    · exact prime_2541157
  · decide +kernel

theorem prime_4754296391681 : Nat.Prime 4754296391681 := by
  apply nodeValid_prime [2, 5, 11, 2137, 19751] ⟨4754296391681, 3, [(2, 11), (5, 1), (11, 1), (2137, 1), (19751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2137
    · exact prime_19751
  · decide +kernel

theorem prime_4754296391939 : Nat.Prime 4754296391939 := by
  apply nodeValid_prime [2, 2377148195969] ⟨4754296391939, 2, [(2, 1), (2377148195969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2377148195969
  · decide +kernel

theorem prime_4758044082773 : Nat.Prime 4758044082773 := by
  apply nodeValid_prime [2, 2137, 7177, 77557] ⟨4758044082773, 2, [(2, 2), (2137, 1), (7177, 1), (77557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2137
    · exact prime_7177
    · exact prime_77557
  · decide +kernel

theorem prime_4758044082989 : Nat.Prime 4758044082989 := by
  apply nodeValid_prime [2, 7, 169930145821] ⟨4758044082989, 2, [(2, 2), (7, 1), (169930145821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_169930145821
  · decide +kernel

theorem prime_4758044140583 : Nat.Prime 4758044140583 := by
  apply nodeValid_prime [2, 17, 6569, 21303467] ⟨4758044140583, 5, [(2, 1), (17, 1), (6569, 1), (21303467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_6569
    · exact prime_21303467
  · decide +kernel

theorem prime_4761793900271 : Nat.Prime 4761793900271 := by
  apply nodeValid_prime [2, 5, 11, 137, 1483, 213067] ⟨4761793900271, 7, [(2, 1), (5, 1), (11, 1), (137, 1), (1483, 1), (213067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_137
    · exact prime_1483
    · exact prime_213067
  · decide +kernel

theorem prime_4761793900631 : Nat.Prime 4761793900631 := by
  apply nodeValid_prime [2, 5, 13, 2817629527] ⟨4761793900631, 11, [(2, 1), (5, 1), (13, 2), (2817629527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2817629527
  · decide +kernel

theorem prime_4761793917137 : Nat.Prime 4761793917137 := by
  apply nodeValid_prime [2, 449, 11321, 58549] ⟨4761793917137, 3, [(2, 4), (449, 1), (11321, 1), (58549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_449
    · exact prime_11321
    · exact prime_58549
  · decide +kernel

theorem prime_4765545706667 : Nat.Prime 4765545706667 := by
  apply nodeValid_prime [2, 560221, 4253273] ⟨4765545706667, 2, [(2, 1), (560221, 1), (4253273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_560221
    · exact prime_4253273
  · decide +kernel

theorem prime_4765545756481 : Nat.Prime 4765545756481 := by
  apply nodeValid_prime [2, 3, 5, 181, 27426023] ⟨4765545756481, 7, [(2, 6), (3, 1), (5, 1), (181, 1), (27426023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
    · exact prime_27426023
  · decide +kernel

theorem prime_4765545757387 : Nat.Prime 4765545757387 := by
  apply nodeValid_prime [2, 3, 2749, 32102891] ⟨4765545757387, 5, [(2, 1), (3, 3), (2749, 1), (32102891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2749
    · exact prime_32102891
  · decide +kernel

theorem prime_4769299499521 : Nat.Prime 4769299499521 := by
  apply nodeValid_prime [2, 3, 5, 109, 541, 10531] ⟨4769299499521, 11, [(2, 9), (3, 1), (5, 1), (109, 1), (541, 1), (10531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_541
    · exact prime_10531
  · decide +kernel

theorem prime_4769299545917 : Nat.Prime 4769299545917 := by
  apply nodeValid_prime [2, 59, 73, 3853, 71849] ⟨4769299545917, 2, [(2, 2), (59, 1), (73, 1), (3853, 1), (71849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_73
    · exact prime_3853
    · exact prime_71849
  · decide +kernel

theorem prime_4769299546901 : Nat.Prime 4769299546901 := by
  apply nodeValid_prime [2, 5, 7, 6813285067] ⟨4769299546901, 2, [(2, 2), (5, 2), (7, 1), (6813285067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6813285067
  · decide +kernel

end Sude.Lucas.Generated
