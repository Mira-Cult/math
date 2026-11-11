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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3217 : Nat.Prime 3217 := by
  apply nodeValid_prime [2, 3, 67] ⟨3217, 5, [(2, 4), (3, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
  · decide +kernel

theorem prime_6229 : Nat.Prime 6229 := by
  apply nodeValid_prime [2, 3, 173] ⟨6229, 2, [(2, 2), (3, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
  · decide +kernel

theorem prime_7741 : Nat.Prime 7741 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨7741, 7, [(2, 2), (3, 2), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_8171 : Nat.Prime 8171 := by
  apply nodeValid_prime [2, 5, 19, 43] ⟨8171, 2, [(2, 1), (5, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_8209 : Nat.Prime 8209 := by
  apply nodeValid_prime [2, 3, 19] ⟨8209, 7, [(2, 4), (3, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_11321 : Nat.Prime 11321 := by
  apply nodeValid_prime [2, 5, 283] ⟨11321, 3, [(2, 3), (5, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_283
  · decide +kernel

theorem prime_13093 : Nat.Prime 13093 := by
  apply nodeValid_prime [2, 3, 1091] ⟨13093, 6, [(2, 2), (3, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
  · decide +kernel

theorem prime_15737 : Nat.Prime 15737 := by
  apply nodeValid_prime [2, 7, 281] ⟨15737, 3, [(2, 3), (7, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_281
  · decide +kernel

theorem prime_16829 : Nat.Prime 16829 := by
  apply nodeValid_prime [2, 7, 601] ⟨16829, 2, [(2, 2), (7, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_601
  · decide +kernel

theorem prime_17839 : Nat.Prime 17839 := by
  apply nodeValid_prime [2, 3, 991] ⟨17839, 6, [(2, 1), (3, 2), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_991
  · decide +kernel

theorem prime_19157 : Nat.Prime 19157 := by
  apply nodeValid_prime [2, 4789] ⟨19157, 2, [(2, 2), (4789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4789
  · decide +kernel

theorem prime_22037 : Nat.Prime 22037 := by
  apply nodeValid_prime [2, 7, 787] ⟨22037, 2, [(2, 2), (7, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_787
  · decide +kernel

theorem prime_22643 : Nat.Prime 22643 := by
  apply nodeValid_prime [2, 11321] ⟨22643, 2, [(2, 1), (11321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11321
  · decide +kernel

theorem prime_22807 : Nat.Prime 22807 := by
  apply nodeValid_prime [2, 3, 7, 181] ⟨22807, 3, [(2, 1), (3, 2), (7, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_181
  · decide +kernel

theorem prime_25919 : Nat.Prime 25919 := by
  apply nodeValid_prime [2, 12959] ⟨25919, 11, [(2, 1), (12959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12959
  · decide +kernel

theorem prime_25939 : Nat.Prime 25939 := by
  apply nodeValid_prime [2, 3, 11, 131] ⟨25939, 3, [(2, 1), (3, 2), (11, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
  · decide +kernel

theorem prime_28597 : Nat.Prime 28597 := by
  apply nodeValid_prime [2, 3, 2383] ⟨28597, 2, [(2, 2), (3, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2383
  · decide +kernel

theorem prime_30773 : Nat.Prime 30773 := by
  apply nodeValid_prime [2, 7, 157] ⟨30773, 3, [(2, 2), (7, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_157
  · decide +kernel

theorem prime_39719 : Nat.Prime 39719 := by
  apply nodeValid_prime [2, 7, 2837] ⟨39719, 7, [(2, 1), (7, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2837
  · decide +kernel

theorem prime_39799 : Nat.Prime 39799 := by
  apply nodeValid_prime [2, 3, 11, 67] ⟨39799, 3, [(2, 1), (3, 3), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_44111 : Nat.Prime 44111 := by
  apply nodeValid_prime [2, 5, 11, 401] ⟨44111, 7, [(2, 1), (5, 1), (11, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_401
  · decide +kernel

theorem prime_45673 : Nat.Prime 45673 := by
  apply nodeValid_prime [2, 3, 11, 173] ⟨45673, 5, [(2, 3), (3, 1), (11, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_173
  · decide +kernel

theorem prime_45971 : Nat.Prime 45971 := by
  apply nodeValid_prime [2, 5, 4597] ⟨45971, 2, [(2, 1), (5, 1), (4597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4597
  · decide +kernel

theorem prime_48281 : Nat.Prime 48281 := by
  apply nodeValid_prime [2, 5, 17, 71] ⟨48281, 3, [(2, 3), (5, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_51503 : Nat.Prime 51503 := by
  apply nodeValid_prime [2, 11, 2341] ⟨51503, 5, [(2, 1), (11, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2341
  · decide +kernel

theorem prime_59791 : Nat.Prime 59791 := by
  apply nodeValid_prime [2, 3, 5, 1993] ⟨59791, 3, [(2, 1), (3, 1), (5, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1993
  · decide +kernel

theorem prime_75619 : Nat.Prime 75619 := by
  apply nodeValid_prime [2, 3, 4201] ⟨75619, 2, [(2, 1), (3, 2), (4201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4201
  · decide +kernel

theorem prime_75989 : Nat.Prime 75989 := by
  apply nodeValid_prime [2, 11, 157] ⟨75989, 2, [(2, 2), (11, 2), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_157
  · decide +kernel

theorem prime_87697 : Nat.Prime 87697 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨87697, 17, [(2, 4), (3, 3), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_88327 : Nat.Prime 88327 := by
  apply nodeValid_prime [2, 3, 7, 701] ⟨88327, 5, [(2, 1), (3, 2), (7, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_701
  · decide +kernel

theorem prime_93559 : Nat.Prime 93559 := by
  apply nodeValid_prime [2, 3, 31, 503] ⟨93559, 3, [(2, 1), (3, 1), (31, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_503
  · decide +kernel

theorem prime_109807 : Nat.Prime 109807 := by
  apply nodeValid_prime [2, 3, 18301] ⟨109807, 5, [(2, 1), (3, 1), (18301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18301
  · decide +kernel

theorem prime_123439 : Nat.Prime 123439 := by
  apply nodeValid_prime [2, 3, 7, 2939] ⟨123439, 6, [(2, 1), (3, 1), (7, 1), (2939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2939
  · decide +kernel

theorem prime_125897 : Nat.Prime 125897 := by
  apply nodeValid_prime [2, 15737] ⟨125897, 3, [(2, 3), (15737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15737
  · decide +kernel

theorem prime_131701 : Nat.Prime 131701 := by
  apply nodeValid_prime [2, 3, 5, 439] ⟨131701, 6, [(2, 2), (3, 1), (5, 2), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_439
  · decide +kernel

theorem prime_137653 : Nat.Prime 137653 := by
  apply nodeValid_prime [2, 3, 11471] ⟨137653, 2, [(2, 2), (3, 1), (11471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11471
  · decide +kernel

theorem prime_144773 : Nat.Prime 144773 := by
  apply nodeValid_prime [2, 17, 2129] ⟨144773, 2, [(2, 2), (17, 1), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2129
  · decide +kernel

theorem prime_171583 : Nat.Prime 171583 := by
  apply nodeValid_prime [2, 3, 28597] ⟨171583, 5, [(2, 1), (3, 1), (28597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28597
  · decide +kernel

theorem prime_175891 : Nat.Prime 175891 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 41] ⟨175891, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_231599 : Nat.Prime 231599 := by
  apply nodeValid_prime [2, 43, 2693] ⟨231599, 7, [(2, 1), (43, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2693
  · decide +kernel

theorem prime_275827 : Nat.Prime 275827 := by
  apply nodeValid_prime [2, 3, 45971] ⟨275827, 3, [(2, 1), (3, 1), (45971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45971
  · decide +kernel

theorem prime_296693 : Nat.Prime 296693 := by
  apply nodeValid_prime [2, 11, 613] ⟨296693, 2, [(2, 2), (11, 2), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_613
  · decide +kernel

theorem prime_309019 : Nat.Prime 309019 := by
  apply nodeValid_prime [2, 3, 51503] ⟨309019, 2, [(2, 1), (3, 1), (51503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51503
  · decide +kernel

theorem prime_331663 : Nat.Prime 331663 := by
  apply nodeValid_prime [2, 3, 167, 331] ⟨331663, 5, [(2, 1), (3, 1), (167, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_331
  · decide +kernel

theorem prime_332623 : Nat.Prime 332623 := by
  apply nodeValid_prime [2, 3, 17, 1087] ⟨332623, 6, [(2, 1), (3, 2), (17, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1087
  · decide +kernel

theorem prime_350087 : Nat.Prime 350087 := by
  apply nodeValid_prime [2, 11, 15913] ⟨350087, 5, [(2, 1), (11, 1), (15913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_15913
  · decide +kernel

theorem prime_354181 : Nat.Prime 354181 := by
  apply nodeValid_prime [2, 3, 5, 5903] ⟨354181, 10, [(2, 2), (3, 1), (5, 1), (5903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5903
  · decide +kernel

theorem prime_421189 : Nat.Prime 421189 := by
  apply nodeValid_prime [2, 3, 35099] ⟨421189, 6, [(2, 2), (3, 1), (35099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35099
  · decide +kernel

theorem prime_427951 : Nat.Prime 427951 := by
  apply nodeValid_prime [2, 3, 5, 317] ⟨427951, 15, [(2, 1), (3, 3), (5, 2), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_317
  · decide +kernel

theorem prime_477941 : Nat.Prime 477941 := by
  apply nodeValid_prime [2, 5, 23, 1039] ⟨477941, 2, [(2, 2), (5, 1), (23, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1039
  · decide +kernel

theorem prime_499139 : Nat.Prime 499139 := by
  apply nodeValid_prime [2, 103, 2423] ⟨499139, 2, [(2, 1), (103, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_2423
  · decide +kernel

theorem prime_664789 : Nat.Prime 664789 := by
  apply nodeValid_prime [2, 3, 55399] ⟨664789, 6, [(2, 2), (3, 1), (55399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55399
  · decide +kernel

theorem prime_756191 : Nat.Prime 756191 := by
  apply nodeValid_prime [2, 5, 75619] ⟨756191, 7, [(2, 1), (5, 1), (75619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_75619
  · decide +kernel

theorem prime_820901 : Nat.Prime 820901 := by
  apply nodeValid_prime [2, 5, 8209] ⟨820901, 2, [(2, 2), (5, 2), (8209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8209
  · decide +kernel

theorem prime_825919 : Nat.Prime 825919 := by
  apply nodeValid_prime [2, 3, 137653] ⟨825919, 6, [(2, 1), (3, 1), (137653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137653
  · decide +kernel

theorem prime_845729 : Nat.Prime 845729 := by
  apply nodeValid_prime [2, 13, 19, 107] ⟨845729, 3, [(2, 5), (13, 1), (19, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_107
  · decide +kernel

theorem prime_862607 : Nat.Prime 862607 := by
  apply nodeValid_prime [2, 31, 13913] ⟨862607, 5, [(2, 1), (31, 1), (13913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_13913
  · decide +kernel

theorem prime_922643 : Nat.Prime 922643 := by
  apply nodeValid_prime [2, 7, 59, 1117] ⟨922643, 2, [(2, 1), (7, 1), (59, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_1117
  · decide +kernel

theorem prime_955883 : Nat.Prime 955883 := by
  apply nodeValid_prime [2, 477941] ⟨955883, 2, [(2, 1), (477941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_477941
  · decide +kernel

theorem prime_1055347 : Nat.Prime 1055347 := by
  apply nodeValid_prime [2, 3, 175891] ⟨1055347, 2, [(2, 1), (3, 1), (175891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_175891
  · decide +kernel

theorem prime_1103309 : Nat.Prime 1103309 := by
  apply nodeValid_prime [2, 275827] ⟨1103309, 2, [(2, 2), (275827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_275827
  · decide +kernel

theorem prime_1148977 : Nat.Prime 1148977 := by
  apply nodeValid_prime [2, 3, 79, 101] ⟨1148977, 5, [(2, 4), (3, 2), (79, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_101
  · decide +kernel

theorem prime_1234391 : Nat.Prime 1234391 := by
  apply nodeValid_prime [2, 5, 123439] ⟨1234391, 7, [(2, 1), (5, 1), (123439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_123439
  · decide +kernel

theorem prime_1343569 : Nat.Prime 1343569 := by
  apply nodeValid_prime [2, 3, 23, 1217] ⟨1343569, 7, [(2, 4), (3, 1), (23, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1217
  · decide +kernel

theorem prime_1502651 : Nat.Prime 1502651 := by
  apply nodeValid_prime [2, 5, 41, 733] ⟨1502651, 2, [(2, 1), (5, 2), (41, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_733
  · decide +kernel

theorem prime_1596059 : Nat.Prime 1596059 := by
  apply nodeValid_prime [2, 181, 4409] ⟨1596059, 2, [(2, 1), (181, 1), (4409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_4409
  · decide +kernel

theorem prime_1684063 : Nat.Prime 1684063 := by
  apply nodeValid_prime [2, 3, 93559] ⟨1684063, 3, [(2, 1), (3, 2), (93559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_93559
  · decide +kernel

theorem prime_1908083 : Nat.Prime 1908083 := by
  apply nodeValid_prime [2, 11, 43, 2017] ⟨1908083, 2, [(2, 1), (11, 1), (43, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_2017
  · decide +kernel

theorem prime_2073101 : Nat.Prime 2073101 := by
  apply nodeValid_prime [2, 5, 20731] ⟨2073101, 2, [(2, 2), (5, 2), (20731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20731
  · decide +kernel

theorem prime_2183681 : Nat.Prime 2183681 := by
  apply nodeValid_prime [2, 5, 853] ⟨2183681, 3, [(2, 9), (5, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_853
  · decide +kernel

theorem prime_2860931 : Nat.Prime 2860931 := by
  apply nodeValid_prime [2, 5, 17, 16829] ⟨2860931, 2, [(2, 1), (5, 1), (17, 1), (16829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_16829
  · decide +kernel

theorem prime_3412159 : Nat.Prime 3412159 := by
  apply nodeValid_prime [2, 3, 691, 823] ⟨3412159, 3, [(2, 1), (3, 1), (691, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_823
  · decide +kernel

theorem prime_3421051 : Nat.Prime 3421051 := by
  apply nodeValid_prime [2, 3, 5, 22807] ⟨3421051, 12, [(2, 1), (3, 1), (5, 2), (22807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22807
  · decide +kernel

theorem prime_3950033 : Nat.Prime 3950033 := by
  apply nodeValid_prime [2, 29, 8513] ⟨3950033, 3, [(2, 4), (29, 1), (8513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_8513
  · decide +kernel

theorem prime_4146203 : Nat.Prime 4146203 := by
  apply nodeValid_prime [2, 2073101] ⟨4146203, 2, [(2, 1), (2073101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2073101
  · decide +kernel

theorem prime_4237333 : Nat.Prime 4237333 := by
  apply nodeValid_prime [2, 3, 11, 47, 683] ⟨4237333, 5, [(2, 2), (3, 1), (11, 1), (47, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_683
  · decide +kernel

theorem prime_4336987 : Nat.Prime 4336987 := by
  apply nodeValid_prime [2, 3, 293, 2467] ⟨4336987, 2, [(2, 1), (3, 1), (293, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_2467
  · decide +kernel

theorem prime_4454399 : Nat.Prime 4454399 := by
  apply nodeValid_prime [2, 13, 19, 71, 127] ⟨4454399, 11, [(2, 1), (13, 1), (19, 1), (71, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_71
    · exact prime_127
  · decide +kernel

theorem prime_7274887 : Nat.Prime 7274887 := by
  apply nodeValid_prime [2, 3, 53, 22877] ⟨7274887, 5, [(2, 1), (3, 1), (53, 1), (22877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_22877
  · decide +kernel

theorem prime_9077741 : Nat.Prime 9077741 := by
  apply nodeValid_prime [2, 5, 7, 59, 157] ⟨9077741, 2, [(2, 2), (5, 1), (7, 2), (59, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_157
  · decide +kernel

theorem prime_9591331 : Nat.Prime 9591331 := by
  apply nodeValid_prime [2, 3, 5, 7, 45673] ⟨9591331, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (45673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_45673
  · decide +kernel

theorem prime_11358209 : Nat.Prime 11358209 := by
  apply nodeValid_prime [2, 47, 59] ⟨11358209, 3, [(2, 12), (47, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_59
  · decide +kernel

theorem prime_18155483 : Nat.Prime 18155483 := by
  apply nodeValid_prime [2, 9077741] ⟨18155483, 2, [(2, 1), (9077741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9077741
  · decide +kernel

theorem prime_18369073 : Nat.Prime 18369073 := by
  apply nodeValid_prime [2, 3, 101, 421] ⟨18369073, 5, [(2, 4), (3, 3), (101, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_421
  · decide +kernel

theorem prime_18912359 : Nat.Prime 18912359 := by
  apply nodeValid_prime [2, 67, 113, 1249] ⟨18912359, 7, [(2, 1), (67, 1), (113, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_113
    · exact prime_1249
  · decide +kernel

theorem prime_19348487 : Nat.Prime 19348487 := by
  apply nodeValid_prime [2, 439, 22037] ⟨19348487, 5, [(2, 1), (439, 1), (22037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_439
    · exact prime_22037
  · decide +kernel

theorem prime_23296289 : Nat.Prime 23296289 := by
  apply nodeValid_prime [2, 157, 4637] ⟨23296289, 3, [(2, 5), (157, 1), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_4637
  · decide +kernel

theorem prime_26498249 : Nat.Prime 26498249 := by
  apply nodeValid_prime [2, 7, 83, 5701] ⟨26498249, 3, [(2, 3), (7, 1), (83, 1), (5701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
    · exact prime_5701
  · decide +kernel

theorem prime_52996499 : Nat.Prime 52996499 := by
  apply nodeValid_prime [2, 26498249] ⟨52996499, 2, [(2, 1), (26498249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26498249
  · decide +kernel

theorem prime_56988739 : Nat.Prime 56988739 := by
  apply nodeValid_prime [2, 3, 1055347] ⟨56988739, 2, [(2, 1), (3, 3), (1055347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1055347
  · decide +kernel

theorem prime_58982899 : Nat.Prime 58982899 := by
  apply nodeValid_prime [2, 3, 13, 756191] ⟨58982899, 2, [(2, 1), (3, 1), (13, 1), (756191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_756191
  · decide +kernel

theorem prime_65966863 : Nat.Prime 65966863 := by
  apply nodeValid_prime [2, 3, 13, 845729] ⟨65966863, 7, [(2, 1), (3, 1), (13, 1), (845729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_845729
  · decide +kernel

theorem prime_67148621 : Nat.Prime 67148621 := by
  apply nodeValid_prime [2, 5, 7, 11, 6229] ⟨67148621, 3, [(2, 2), (5, 1), (7, 2), (11, 1), (6229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_6229
  · decide +kernel

theorem prime_77825633 : Nat.Prime 77825633 := by
  apply nodeValid_prime [2, 619, 3929] ⟨77825633, 3, [(2, 5), (619, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_3929
  · decide +kernel

theorem prime_87517627 : Nat.Prime 87517627 := by
  apply nodeValid_prime [2, 3, 7, 109, 2731] ⟨87517627, 2, [(2, 1), (3, 1), (7, 2), (109, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_109
    · exact prime_2731
  · decide +kernel

theorem prime_115516711 : Nat.Prime 115516711 := by
  apply nodeValid_prime [2, 3, 5, 67, 19157] ⟨115516711, 6, [(2, 1), (3, 2), (5, 1), (67, 1), (19157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_19157
  · decide +kernel

theorem prime_128954827 : Nat.Prime 128954827 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 17, 421] ⟨128954827, 2, [(2, 1), (3, 2), (7, 1), (11, 1), (13, 1), (17, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_421
  · decide +kernel

theorem prime_141761993 : Nat.Prime 141761993 := by
  apply nodeValid_prime [2, 223, 229, 347] ⟨141761993, 3, [(2, 3), (223, 1), (229, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_229
    · exact prime_347
  · decide +kernel

theorem prime_144579131 : Nat.Prime 144579131 := by
  apply nodeValid_prime [2, 5, 1571, 9203] ⟨144579131, 6, [(2, 1), (5, 1), (1571, 1), (9203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1571
    · exact prime_9203
  · decide +kernel

theorem prime_194189263 : Nat.Prime 194189263 := by
  apply nodeValid_prime [2, 3, 2089, 15493] ⟨194189263, 3, [(2, 1), (3, 1), (2089, 1), (15493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2089
    · exact prime_15493
  · decide +kernel

theorem prime_286860341 : Nat.Prime 286860341 := by
  apply nodeValid_prime [2, 5, 13, 1103309] ⟨286860341, 2, [(2, 2), (5, 1), (13, 1), (1103309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1103309
  · decide +kernel

theorem prime_364090481 : Nat.Prime 364090481 := by
  apply nodeValid_prime [2, 5, 13, 350087] ⟨364090481, 3, [(2, 4), (5, 1), (13, 1), (350087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_350087
  · decide +kernel

theorem prime_384264967 : Nat.Prime 384264967 := by
  apply nodeValid_prime [2, 3, 67, 955883] ⟨384264967, 3, [(2, 1), (3, 1), (67, 1), (955883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_955883
  · decide +kernel

theorem prime_619508629 : Nat.Prime 619508629 := by
  apply nodeValid_prime [2, 3, 17, 383, 881] ⟨619508629, 2, [(2, 2), (3, 3), (17, 1), (383, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_383
    · exact prime_881
  · decide +kernel

theorem prime_700724599 : Nat.Prime 700724599 := by
  apply nodeValid_prime [2, 3, 7, 17, 19, 47, 157] ⟨700724599, 3, [(2, 1), (3, 1), (7, 2), (17, 1), (19, 1), (47, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
    · exact prime_47
    · exact prime_157
  · decide +kernel

theorem prime_779655119 : Nat.Prime 779655119 := by
  apply nodeValid_prime [2, 11, 71, 499139] ⟨779655119, 11, [(2, 1), (11, 1), (71, 1), (499139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_499139
  · decide +kernel

theorem prime_884745349 : Nat.Prime 884745349 := by
  apply nodeValid_prime [2, 3, 17, 4336987] ⟨884745349, 6, [(2, 2), (3, 1), (17, 1), (4336987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4336987
  · decide +kernel

theorem prime_1025797303 : Nat.Prime 1025797303 := by
  apply nodeValid_prime [2, 3, 56988739] ⟨1025797303, 3, [(2, 1), (3, 2), (56988739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56988739
  · decide +kernel

theorem prime_1032755429 : Nat.Prime 1032755429 := by
  apply nodeValid_prime [2, 613, 421189] ⟨1032755429, 2, [(2, 2), (613, 1), (421189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_421189
  · decide +kernel

theorem prime_1265788871 : Nat.Prime 1265788871 := by
  apply nodeValid_prime [2, 5, 37, 3421051] ⟨1265788871, 7, [(2, 1), (5, 1), (37, 1), (3421051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_3421051
  · decide +kernel

theorem prime_1288644271 : Nat.Prime 1288644271 := by
  apply nodeValid_prime [2, 3, 5, 31, 179, 7741] ⟨1288644271, 3, [(2, 1), (3, 1), (5, 1), (31, 1), (179, 1), (7741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_179
    · exact prime_7741
  · decide +kernel

theorem prime_1559310239 : Nat.Prime 1559310239 := by
  apply nodeValid_prime [2, 779655119] ⟨1559310239, 7, [(2, 1), (779655119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_779655119
  · decide +kernel

theorem prime_3610735157 : Nat.Prime 3610735157 := by
  apply nodeValid_prime [2, 7, 128954827] ⟨3610735157, 2, [(2, 2), (7, 1), (128954827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_128954827
  · decide +kernel

theorem prime_3869697401 : Nat.Prime 3869697401 := by
  apply nodeValid_prime [2, 5, 19348487] ⟨3869697401, 3, [(2, 3), (5, 2), (19348487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19348487
  · decide +kernel

theorem prime_4158601597 : Nat.Prime 4158601597 := by
  apply nodeValid_prime [2, 3, 115516711] ⟨4158601597, 2, [(2, 2), (3, 2), (115516711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115516711
  · decide +kernel

theorem prime_4306351807 : Nat.Prime 4306351807 := by
  apply nodeValid_prime [2, 3, 1033, 231599] ⟨4306351807, 5, [(2, 1), (3, 2), (1033, 1), (231599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
    · exact prime_231599
  · decide +kernel

theorem prime_5603445577 : Nat.Prime 5603445577 := by
  apply nodeValid_prime [2, 3, 77825633] ⟨5603445577, 5, [(2, 3), (3, 2), (77825633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_77825633
  · decide +kernel

theorem prime_5737206821 : Nat.Prime 5737206821 := by
  apply nodeValid_prime [2, 5, 286860341] ⟨5737206821, 2, [(2, 2), (5, 1), (286860341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_286860341
  · decide +kernel

theorem prime_6623506693 : Nat.Prime 6623506693 := by
  apply nodeValid_prime [2, 3, 11, 127, 131701] ⟨6623506693, 5, [(2, 2), (3, 2), (11, 1), (127, 1), (131701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_127
    · exact prime_131701
  · decide +kernel

theorem prime_7077962839 : Nat.Prime 7077962839 := by
  apply nodeValid_prime [2, 3, 47, 569, 44111] ⟨7077962839, 3, [(2, 1), (3, 1), (47, 1), (569, 1), (44111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_569
    · exact prime_44111
  · decide +kernel

theorem prime_7692247463 : Nat.Prime 7692247463 := by
  apply nodeValid_prime [2, 401, 9591331] ⟨7692247463, 5, [(2, 1), (401, 1), (9591331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_401
    · exact prime_9591331
  · decide +kernel

theorem prime_14613774403 : Nat.Prime 14613774403 := by
  apply nodeValid_prime [2, 3, 41, 541, 109807] ⟨14613774403, 3, [(2, 1), (3, 1), (41, 1), (541, 1), (109807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_541
    · exact prime_109807
  · decide +kernel

theorem prime_18108643349 : Nat.Prime 18108643349 := by
  apply nodeValid_prime [2, 19, 41, 47, 53, 2333] ⟨18108643349, 2, [(2, 2), (19, 1), (41, 1), (47, 1), (53, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_47
    · exact prime_53
    · exact prime_2333
  · decide +kernel

theorem prime_35389813961 : Nat.Prime 35389813961 := by
  apply nodeValid_prime [2, 5, 884745349] ⟨35389813961, 3, [(2, 3), (5, 1), (884745349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_884745349
  · decide +kernel

theorem prime_39741040159 : Nat.Prime 39741040159 := by
  apply nodeValid_prime [2, 3, 6623506693] ⟨39741040159, 3, [(2, 1), (3, 1), (6623506693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6623506693
  · decide +kernel

theorem prime_74358390889 : Nat.Prime 74358390889 := by
  apply nodeValid_prime [2, 3, 1032755429] ⟨74358390889, 11, [(2, 3), (3, 2), (1032755429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1032755429
  · decide +kernel

theorem prime_114744136421 : Nat.Prime 114744136421 := by
  apply nodeValid_prime [2, 5, 5737206821] ⟨114744136421, 10, [(2, 2), (5, 1), (5737206821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5737206821
  · decide +kernel

theorem prime_336601654567 : Nat.Prime 336601654567 := by
  apply nodeValid_prime [2, 3, 109, 5827, 88327] ⟨336601654567, 5, [(2, 1), (3, 1), (109, 1), (5827, 1), (88327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_5827
    · exact prime_88327
  · decide +kernel

theorem prime_1338451036003 : Nat.Prime 1338451036003 := by
  apply nodeValid_prime [2, 3, 74358390889] ⟨1338451036003, 2, [(2, 1), (3, 2), (74358390889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_74358390889
  · decide +kernel

theorem prime_1338451036133 : Nat.Prime 1338451036133 := by
  apply nodeValid_prime [2, 7, 39799, 171583] ⟨1338451036133, 2, [(2, 2), (7, 2), (39799, 1), (171583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_39799
    · exact prime_171583
  · decide +kernel

theorem prime_1338451058563 : Nat.Prime 1338451058563 := by
  apply nodeValid_prime [2, 3, 29, 7692247463] ⟨1338451058563, 3, [(2, 1), (3, 1), (29, 1), (7692247463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_7692247463
  · decide +kernel

theorem prime_1340039607827 : Nat.Prime 1340039607827 := by
  apply nodeValid_prime [2, 37, 18108643349] ⟨1340039607827, 2, [(2, 1), (37, 1), (18108643349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_18108643349
  · decide +kernel

theorem prime_1340039610593 : Nat.Prime 1340039610593 := by
  apply nodeValid_prime [2, 125897, 332623] ⟨1340039610593, 3, [(2, 5), (125897, 1), (332623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_125897
    · exact prime_332623
  · decide +kernel

theorem prime_1340039611919 : Nat.Prime 1340039611919 := by
  apply nodeValid_prime [2, 7, 461, 4237333] ⟨1340039611919, 7, [(2, 1), (7, 3), (461, 1), (4237333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_461
    · exact prime_4237333
  · decide +kernel

theorem prime_1341629434853 : Nat.Prime 1341629434853 := by
  apply nodeValid_prime [2, 7, 37, 233, 263, 3019] ⟨1341629434853, 2, [(2, 2), (7, 2), (37, 1), (233, 1), (263, 1), (3019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_233
    · exact prime_263
    · exact prime_3019
  · decide +kernel

theorem prime_1341629446741 : Nat.Prime 1341629446741 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 6703, 17839] ⟨1341629446741, 7, [(2, 2), (3, 1), (5, 1), (11, 1), (17, 1), (6703, 1), (17839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_6703
    · exact prime_17839
  · decide +kernel

theorem prime_1341629447581 : Nat.Prime 1341629447581 := by
  apply nodeValid_prime [2, 3, 5, 37, 67148621] ⟨1341629447581, 6, [(2, 2), (3, 3), (5, 1), (37, 1), (67148621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_67148621
  · decide +kernel

theorem prime_1343220539197 : Nat.Prime 1343220539197 := by
  apply nodeValid_prime [2, 3, 1279, 87517627] ⟨1343220539197, 2, [(2, 2), (3, 1), (1279, 1), (87517627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
    · exact prime_87517627
  · decide +kernel

theorem prime_1343220585121 : Nat.Prime 1343220585121 := by
  apply nodeValid_prime [2, 3, 5, 337, 922643] ⟨1343220585121, 11, [(2, 5), (3, 3), (5, 1), (337, 1), (922643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_337
    · exact prime_922643
  · decide +kernel

theorem prime_1343220585907 : Nat.Prime 1343220585907 := by
  apply nodeValid_prime [2, 3, 30773, 7274887] ⟨1343220585907, 7, [(2, 1), (3, 1), (30773, 1), (7274887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30773
    · exact prime_7274887
  · decide +kernel

theorem prime_1344812930519 : Nat.Prime 1344812930519 := by
  apply nodeValid_prime [2, 19, 35389813961] ⟨1344812930519, 7, [(2, 1), (19, 1), (35389813961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_35389813961
  · decide +kernel

theorem prime_1344812936777 : Nat.Prime 1344812936777 := by
  apply nodeValid_prime [2, 47, 197, 18155483] ⟨1344812936777, 3, [(2, 3), (47, 1), (197, 1), (18155483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_197
    · exact prime_18155483
  · decide +kernel

theorem prime_1344812939411 : Nat.Prime 1344812939411 := by
  apply nodeValid_prime [2, 5, 19, 7077962839] ⟨1344812939411, 2, [(2, 1), (5, 1), (19, 1), (7077962839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_7077962839
  · decide +kernel

theorem prime_1346406598739 : Nat.Prime 1346406598739 := by
  apply nodeValid_prime [2, 43, 364090481] ⟨1346406598739, 2, [(2, 1), (43, 2), (364090481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_364090481
  · decide +kernel

theorem prime_1346406617729 : Nat.Prime 1346406617729 := by
  apply nodeValid_prime [2, 7829, 1343569] ⟨1346406617729, 3, [(2, 7), (7829, 1), (1343569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7829
    · exact prime_1343569
  · decide +kernel

theorem prime_1346406618269 : Nat.Prime 1346406618269 := by
  apply nodeValid_prime [2, 336601654567] ⟨1346406618269, 2, [(2, 2), (336601654567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_336601654567
  · decide +kernel

theorem prime_1348001503447 : Nat.Prime 1348001503447 := by
  apply nodeValid_prime [2, 3, 13, 31, 1879, 296693] ⟨1348001503447, 3, [(2, 1), (3, 1), (13, 1), (31, 1), (1879, 1), (296693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_1879
    · exact prime_296693
  · decide +kernel

theorem prime_1348001504237 : Nat.Prime 1348001504237 := by
  apply nodeValid_prime [2, 877, 384264967] ⟨1348001504237, 2, [(2, 2), (877, 1), (384264967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_877
    · exact prime_384264967
  · decide +kernel

theorem prime_1348001538217 : Nat.Prime 1348001538217 := by
  apply nodeValid_prime [2, 3, 1019, 3109, 17729] ⟨1348001538217, 10, [(2, 3), (3, 1), (1019, 1), (3109, 1), (17729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1019
    · exact prime_3109
    · exact prime_17729
  · decide +kernel

theorem prime_1349597761037 : Nat.Prime 1349597761037 := by
  apply nodeValid_prime [2, 7, 463, 2621, 39719] ⟨1349597761037, 2, [(2, 2), (7, 1), (463, 1), (2621, 1), (39719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_463
    · exact prime_2621
    · exact prime_39719
  · decide +kernel

theorem prime_1349597837879 : Nat.Prime 1349597837879 := by
  apply nodeValid_prime [2, 309019, 2183681] ⟨1349597837879, 7, [(2, 1), (309019, 1), (2183681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_309019
    · exact prime_2183681
  · decide +kernel

theorem prime_1349597840183 : Nat.Prime 1349597840183 := by
  apply nodeValid_prime [2, 17, 29, 67, 2687, 7603] ⟨1349597840183, 5, [(2, 1), (17, 1), (29, 1), (67, 1), (2687, 1), (7603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_67
    · exact prime_2687
    · exact prime_7603
  · decide +kernel

theorem prime_1351195259059 : Nat.Prime 1351195259059 := by
  apply nodeValid_prime [2, 3, 2203, 11358209] ⟨1351195259059, 3, [(2, 1), (3, 3), (2203, 1), (11358209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2203
    · exact prime_11358209
  · decide +kernel

theorem prime_1351195363601 : Nat.Prime 1351195363601 := by
  apply nodeValid_prime [2, 5, 23333, 144773] ⟨1351195363601, 3, [(2, 4), (5, 2), (23333, 1), (144773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23333
    · exact prime_144773
  · decide +kernel

theorem prime_1351195365407 : Nat.Prime 1351195365407 := by
  apply nodeValid_prime [2, 17, 39741040159] ⟨1351195365407, 5, [(2, 1), (17, 1), (39741040159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_39741040159
  · decide +kernel

theorem prime_1352794030031 : Nat.Prime 1352794030031 := by
  apply nodeValid_prime [2, 5, 281, 419, 1148977] ⟨1352794030031, 11, [(2, 1), (5, 1), (281, 1), (419, 1), (1148977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_281
    · exact prime_419
    · exact prime_1148977
  · decide +kernel

theorem prime_1352794071457 : Nat.Prime 1352794071457 := by
  apply nodeValid_prime [2, 3, 109, 1596059] ⟨1352794071457, 5, [(2, 5), (3, 5), (109, 1), (1596059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1596059
  · decide +kernel

theorem prime_1352794073101 : Nat.Prime 1352794073101 := by
  apply nodeValid_prime [2, 3, 5, 263, 661, 25939] ⟨1352794073101, 2, [(2, 2), (3, 1), (5, 2), (263, 1), (661, 1), (25939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
    · exact prime_661
    · exact prime_25939
  · decide +kernel

theorem prime_1354394081123 : Nat.Prime 1354394081123 := by
  apply nodeValid_prime [2, 17, 281, 141761993] ⟨1354394081123, 2, [(2, 1), (17, 1), (281, 1), (141761993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_281
    · exact prime_141761993
  · decide +kernel

theorem prime_1354394090351 : Nat.Prime 1354394090351 := by
  apply nodeValid_prime [2, 5, 7, 3869697401] ⟨1354394090351, 7, [(2, 1), (5, 2), (7, 1), (3869697401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3869697401
  · decide +kernel

theorem prime_1354394091971 : Nat.Prime 1354394091971 := by
  apply nodeValid_prime [2, 5, 107, 1265788871] ⟨1354394091971, 6, [(2, 1), (5, 1), (107, 1), (1265788871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_1265788871
  · decide +kernel

theorem prime_1355995417379 : Nat.Prime 1355995417379 := by
  apply nodeValid_prime [2, 7, 19, 37, 389, 354181] ⟨1355995417379, 2, [(2, 1), (7, 1), (19, 1), (37, 1), (389, 1), (354181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_37
    · exact prime_389
    · exact prime_354181
  · decide +kernel

theorem prime_1355995466039 : Nat.Prime 1355995466039 := by
  apply nodeValid_prime [2, 820901, 825919] ⟨1355995466039, 7, [(2, 1), (820901, 1), (825919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_820901
    · exact prime_825919
  · decide +kernel

theorem prime_1355995466071 : Nat.Prime 1355995466071 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 61, 2860931] ⟨1355995466071, 15, [(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (61, 1), (2860931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_61
    · exact prime_2860931
  · decide +kernel

theorem prime_1357598034493 : Nat.Prime 1357598034493 := by
  apply nodeValid_prime [2, 3, 7, 13093, 1234391] ⟨1357598034493, 2, [(2, 2), (3, 1), (7, 1), (13093, 1), (1234391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13093
    · exact prime_1234391
  · decide +kernel

theorem prime_1357598040091 : Nat.Prime 1357598040091 := by
  apply nodeValid_prime [2, 3, 5, 313, 144579131] ⟨1357598040091, 3, [(2, 1), (3, 1), (5, 1), (313, 1), (144579131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_313
    · exact prime_144579131
  · decide +kernel

theorem prime_1357598040541 : Nat.Prime 1357598040541 := by
  apply nodeValid_prime [2, 3, 5, 7, 65966863] ⟨1357598040541, 6, [(2, 2), (3, 1), (5, 1), (7, 3), (65966863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_65966863
  · decide +kernel

theorem prime_1359201924557 : Nat.Prime 1359201924557 := by
  apply nodeValid_prime [2, 7, 823, 58982899] ⟨1359201924557, 2, [(2, 2), (7, 1), (823, 1), (58982899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_823
    · exact prime_58982899
  · decide +kernel

theorem prime_1359201924937 : Nat.Prime 1359201924937 := by
  apply nodeValid_prime [2, 3, 17, 739, 1502651] ⟨1359201924937, 5, [(2, 3), (3, 2), (17, 1), (739, 1), (1502651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_739
    · exact prime_1502651
  · decide +kernel

theorem prime_1359201932027 : Nat.Prime 1359201932027 := by
  apply nodeValid_prime [2, 1097, 619508629] ⟨1359201932027, 2, [(2, 1), (1097, 1), (619508629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1097
    · exact prime_619508629
  · decide +kernel

theorem prime_1360807107151 : Nat.Prime 1360807107151 := by
  apply nodeValid_prime [2, 3, 5, 5387, 1684063] ⟨1360807107151, 14, [(2, 1), (3, 1), (5, 2), (5387, 1), (1684063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5387
    · exact prime_1684063
  · decide +kernel

theorem prime_1360807171013 : Nat.Prime 1360807171013 := by
  apply nodeValid_prime [2, 79, 4306351807] ⟨1360807171013, 2, [(2, 2), (79, 1), (4306351807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_4306351807
  · decide +kernel

theorem prime_1360807171259 : Nat.Prime 1360807171259 := by
  apply nodeValid_prime [2, 971, 700724599] ⟨1360807171259, 2, [(2, 1), (971, 1), (700724599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_971
    · exact prime_700724599
  · decide +kernel

theorem prime_1362413569343 : Nat.Prime 1362413569343 := by
  apply nodeValid_prime [2, 7, 3121, 4454399] ⟨1362413569343, 5, [(2, 1), (7, 2), (3121, 1), (4454399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3121
    · exact prime_4454399
  · decide +kernel

theorem prime_1362413573299 : Nat.Prime 1362413573299 := by
  apply nodeValid_prime [2, 3, 19, 23296289] ⟨1362413573299, 2, [(2, 1), (3, 4), (19, 2), (23296289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23296289
  · decide +kernel

theorem prime_1362413573321 : Nat.Prime 1362413573321 := by
  apply nodeValid_prime [2, 5, 59, 22273, 25919] ⟨1362413573321, 3, [(2, 3), (5, 1), (59, 1), (22273, 1), (25919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_22273
    · exact prime_25919
  · decide +kernel

theorem prime_1364021292899 : Nat.Prime 1364021292899 := by
  apply nodeValid_prime [2, 11, 227, 8171, 33427] ⟨1364021292899, 2, [(2, 1), (11, 1), (227, 1), (8171, 1), (33427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_227
    · exact prime_8171
    · exact prime_33427
  · decide +kernel

theorem prime_1364021293321 : Nat.Prime 1364021293321 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 101, 48281] ⟨1364021293321, 29, [(2, 3), (3, 3), (5, 1), (7, 1), (37, 1), (101, 1), (48281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_101
    · exact prime_48281
  · decide +kernel

theorem prime_1364021323817 : Nat.Prime 1364021323817 := by
  apply nodeValid_prime [2, 41, 4158601597] ⟨1364021323817, 3, [(2, 3), (41, 1), (4158601597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_4158601597
  · decide +kernel

theorem prime_1365630363113 : Nat.Prime 1365630363113 := by
  apply nodeValid_prime [2, 9293, 18369073] ⟨1365630363113, 3, [(2, 3), (9293, 1), (18369073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9293
    · exact prime_18369073
  · decide +kernel

theorem prime_1365630386207 : Nat.Prime 1365630386207 := by
  apply nodeValid_prime [2, 3089, 3697, 59791] ⟨1365630386207, 5, [(2, 1), (3089, 1), (3697, 1), (59791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3089
    · exact prime_3697
    · exact prime_59791
  · decide +kernel

theorem prime_1365630386359 : Nat.Prime 1365630386359 := by
  apply nodeValid_prime [2, 3, 7, 379, 1129, 75989] ⟨1365630386359, 3, [(2, 1), (3, 1), (7, 1), (379, 1), (1129, 1), (75989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_379
    · exact prime_1129
    · exact prime_75989
  · decide +kernel

theorem prime_1367240689817 : Nat.Prime 1367240689817 := by
  apply nodeValid_prime [2, 43, 2083, 1908083] ⟨1367240689817, 3, [(2, 3), (43, 1), (2083, 1), (1908083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2083
    · exact prime_1908083
  · decide +kernel

theorem prime_1367240720789 : Nat.Prime 1367240720789 := by
  apply nodeValid_prime [2, 61, 5603445577] ⟨1367240720789, 2, [(2, 2), (61, 1), (5603445577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_5603445577
  · decide +kernel

theorem prime_1367240721071 : Nat.Prime 1367240721071 := by
  apply nodeValid_prime [2, 5, 7, 22643, 862607] ⟨1367240721071, 11, [(2, 1), (5, 1), (7, 1), (22643, 1), (862607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_22643
    · exact prime_862607
  · decide +kernel

theorem prime_1368852300149 : Nat.Prime 1368852300149 := by
  apply nodeValid_prime [2, 1213, 3217, 87697] ⟨1368852300149, 2, [(2, 2), (1213, 1), (3217, 1), (87697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1213
    · exact prime_3217
    · exact prime_87697
  · decide +kernel

theorem prime_1368852335639 : Nat.Prime 1368852335639 := by
  apply nodeValid_prime [2, 383, 431, 4146203] ⟨1368852335639, 17, [(2, 1), (383, 1), (431, 1), (4146203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_431
    · exact prime_4146203
  · decide +kernel

theorem prime_1368852335887 : Nat.Prime 1368852335887 := by
  apply nodeValid_prime [2, 3, 7, 37, 223, 3950033] ⟨1368852335887, 6, [(2, 1), (3, 1), (7, 1), (37, 1), (223, 1), (3950033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_223
    · exact prime_3950033
  · decide +kernel

theorem prime_1370465182577 : Nat.Prime 1370465182577 := by
  apply nodeValid_prime [2, 7, 647, 18912359] ⟨1370465182577, 3, [(2, 4), (7, 1), (647, 1), (18912359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_647
    · exact prime_18912359
  · decide +kernel

theorem prime_1370465182657 : Nat.Prime 1370465182657 := by
  apply nodeValid_prime [2, 3, 1193, 664789] ⟨1370465182657, 5, [(2, 6), (3, 3), (1193, 1), (664789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1193
    · exact prime_664789
  · decide +kernel

theorem prime_1370465196809 : Nat.Prime 1370465196809 := by
  apply nodeValid_prime [2, 167, 1025797303] ⟨1370465196809, 3, [(2, 3), (167, 1), (1025797303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_1025797303
  · decide +kernel

theorem prime_1372079359111 : Nat.Prime 1372079359111 := by
  apply nodeValid_prime [2, 3, 5, 863, 52996499] ⟨1372079359111, 3, [(2, 1), (3, 1), (5, 1), (863, 1), (52996499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_863
    · exact prime_52996499
  · decide +kernel

theorem prime_1372079359661 : Nat.Prime 1372079359661 := by
  apply nodeValid_prime [2, 5, 19, 3610735157] ⟨1372079359661, 3, [(2, 2), (5, 1), (19, 1), (3610735157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3610735157
  · decide +kernel

theorem prime_1372079378161 : Nat.Prime 1372079378161 := by
  apply nodeValid_prime [2, 3, 5, 61, 73, 427951] ⟨1372079378161, 11, [(2, 4), (3, 2), (5, 1), (61, 1), (73, 1), (427951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_73
    · exact prime_427951
  · decide +kernel

theorem prime_1373694792887 : Nat.Prime 1373694792887 := by
  apply nodeValid_prime [2, 13, 41, 1288644271] ⟨1373694792887, 5, [(2, 1), (13, 1), (41, 1), (1288644271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_1288644271
  · decide +kernel

theorem prime_1373694793883 : Nat.Prime 1373694793883 := by
  apply nodeValid_prime [2, 47, 14613774403] ⟨1373694793883, 2, [(2, 1), (47, 1), (14613774403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_14613774403
  · decide +kernel

theorem prime_1373694846463 : Nat.Prime 1373694846463 := by
  apply nodeValid_prime [2, 3, 131, 194189263] ⟨1373694846463, 3, [(2, 1), (3, 3), (131, 1), (194189263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_194189263
  · decide +kernel

theorem prime_1375311605383 : Nat.Prime 1375311605383 := by
  apply nodeValid_prime [2, 3, 11, 13, 179, 331663] ⟨1375311605383, 3, [(2, 1), (3, 4), (11, 1), (13, 1), (179, 1), (331663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_179
    · exact prime_331663
  · decide +kernel

theorem prime_1375311630799 : Nat.Prime 1375311630799 := by
  apply nodeValid_prime [2, 3, 7, 1559310239] ⟨1375311630799, 3, [(2, 1), (3, 2), (7, 2), (1559310239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1559310239
  · decide +kernel

theorem prime_1375311630859 : Nat.Prime 1375311630859 := by
  apply nodeValid_prime [2, 3, 11, 31, 197, 3412159] ⟨1375311630859, 2, [(2, 1), (3, 1), (11, 1), (31, 1), (197, 1), (3412159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_197
    · exact prime_3412159
  · decide +kernel

theorem prime_1376929636861 : Nat.Prime 1376929636861 := by
  apply nodeValid_prime [2, 3, 5, 31, 73, 179, 181, 313] ⟨1376929636861, 2, [(2, 2), (3, 1), (5, 1), (31, 1), (73, 1), (179, 1), (181, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_73
    · exact prime_179
    · exact prime_181
    · exact prime_313
  · decide +kernel

theorem prime_1376929637053 : Nat.Prime 1376929637053 := by
  apply nodeValid_prime [2, 3, 114744136421] ⟨1376929637053, 2, [(2, 2), (3, 1), (114744136421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_114744136421
  · decide +kernel

theorem prime_1376929655303 : Nat.Prime 1376929655303 := by
  apply nodeValid_prime [2, 19, 467, 4049, 19163] ⟨1376929655303, 5, [(2, 1), (19, 1), (467, 1), (4049, 1), (19163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_467
    · exact prime_4049
    · exact prime_19163
  · decide +kernel

end Sude.Lucas.Generated
