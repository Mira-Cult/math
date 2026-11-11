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
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9551 : Nat.Prime 9551 := by
  apply nodeValid_prime [2, 5, 191] ⟨9551, 11, [(2, 1), (5, 2), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_9739 : Nat.Prime 9739 := by
  apply nodeValid_prime [2, 3, 541] ⟨9739, 3, [(2, 1), (3, 2), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541
  · decide +kernel

theorem prime_10357 : Nat.Prime 10357 := by
  apply nodeValid_prime [2, 3, 863] ⟨10357, 2, [(2, 2), (3, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863
  · decide +kernel

theorem prime_11633 : Nat.Prime 11633 := by
  apply nodeValid_prime [2, 727] ⟨11633, 3, [(2, 4), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_727
  · decide +kernel

theorem prime_13381 : Nat.Prime 13381 := by
  apply nodeValid_prime [2, 3, 5, 223] ⟨13381, 10, [(2, 2), (3, 1), (5, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
  · decide +kernel

theorem prime_13619 : Nat.Prime 13619 := by
  apply nodeValid_prime [2, 11, 619] ⟨13619, 2, [(2, 1), (11, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_619
  · decide +kernel

theorem prime_14551 : Nat.Prime 14551 := by
  apply nodeValid_prime [2, 3, 5, 97] ⟨14551, 3, [(2, 1), (3, 1), (5, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_18917 : Nat.Prime 18917 := by
  apply nodeValid_prime [2, 4729] ⟨18917, 2, [(2, 2), (4729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4729
  · decide +kernel

theorem prime_18979 : Nat.Prime 18979 := by
  apply nodeValid_prime [2, 3, 3163] ⟨18979, 2, [(2, 1), (3, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3163
  · decide +kernel

theorem prime_19489 : Nat.Prime 19489 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨19489, 19, [(2, 5), (3, 1), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_20477 : Nat.Prime 20477 := by
  apply nodeValid_prime [2, 5119] ⟨20477, 2, [(2, 2), (5119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5119
  · decide +kernel

theorem prime_21383 : Nat.Prime 21383 := by
  apply nodeValid_prime [2, 10691] ⟨21383, 5, [(2, 1), (10691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10691
  · decide +kernel

theorem prime_24133 : Nat.Prime 24133 := by
  apply nodeValid_prime [2, 3, 2011] ⟨24133, 6, [(2, 2), (3, 1), (2011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2011
  · decide +kernel

theorem prime_31513 : Nat.Prime 31513 := by
  apply nodeValid_prime [2, 3, 13, 101] ⟨31513, 7, [(2, 3), (3, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_32029 : Nat.Prime 32029 := by
  apply nodeValid_prime [2, 3, 17, 157] ⟨32029, 2, [(2, 2), (3, 1), (17, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_157
  · decide +kernel

theorem prime_34261 : Nat.Prime 34261 := by
  apply nodeValid_prime [2, 3, 5, 571] ⟨34261, 2, [(2, 2), (3, 1), (5, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_571
  · decide +kernel

theorem prime_34739 : Nat.Prime 34739 := by
  apply nodeValid_prime [2, 11, 1579] ⟨34739, 6, [(2, 1), (11, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1579
  · decide +kernel

theorem prime_38377 : Nat.Prime 38377 := by
  apply nodeValid_prime [2, 3, 13, 41] ⟨38377, 5, [(2, 3), (3, 2), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_39343 : Nat.Prime 39343 := by
  apply nodeValid_prime [2, 3, 79, 83] ⟨39343, 3, [(2, 1), (3, 1), (79, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_83
  · decide +kernel

theorem prime_47093 : Nat.Prime 47093 := by
  apply nodeValid_prime [2, 61, 193] ⟨47093, 2, [(2, 2), (61, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_193
  · decide +kernel

theorem prime_59621 : Nat.Prime 59621 := by
  apply nodeValid_prime [2, 5, 11, 271] ⟨59621, 3, [(2, 2), (5, 1), (11, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_271
  · decide +kernel

theorem prime_59671 : Nat.Prime 59671 := by
  apply nodeValid_prime [2, 3, 5, 13, 17] ⟨59671, 12, [(2, 1), (3, 3), (5, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_60761 : Nat.Prime 60761 := by
  apply nodeValid_prime [2, 5, 7, 31] ⟨60761, 6, [(2, 3), (5, 1), (7, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_79847 : Nat.Prime 79847 := by
  apply nodeValid_prime [2, 13, 37, 83] ⟨79847, 5, [(2, 1), (13, 1), (37, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_83
  · decide +kernel

theorem prime_80263 : Nat.Prime 80263 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨80263, 3, [(2, 1), (3, 2), (7, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_82567 : Nat.Prime 82567 := by
  apply nodeValid_prime [2, 3, 11, 139] ⟨82567, 3, [(2, 1), (3, 3), (11, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
  · decide +kernel

theorem prime_129011 : Nat.Prime 129011 := by
  apply nodeValid_prime [2, 5, 7, 19, 97] ⟨129011, 2, [(2, 1), (5, 1), (7, 1), (19, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_97
  · decide +kernel

theorem prime_131251 : Nat.Prime 131251 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨131251, 7, [(2, 1), (3, 1), (5, 5), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_141871 : Nat.Prime 141871 := by
  apply nodeValid_prime [2, 3, 5, 4729] ⟨141871, 6, [(2, 1), (3, 1), (5, 1), (4729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4729
  · decide +kernel

theorem prime_146833 : Nat.Prime 146833 := by
  apply nodeValid_prime [2, 3, 7, 19, 23] ⟨146833, 10, [(2, 4), (3, 1), (7, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_153509 : Nat.Prime 153509 := by
  apply nodeValid_prime [2, 38377] ⟨153509, 2, [(2, 2), (38377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38377
  · decide +kernel

theorem prime_155377 : Nat.Prime 155377 := by
  apply nodeValid_prime [2, 3, 13, 83] ⟨155377, 5, [(2, 4), (3, 2), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_199889 : Nat.Prime 199889 := by
  apply nodeValid_prime [2, 13, 31] ⟨199889, 6, [(2, 4), (13, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_211373 : Nat.Prime 211373 := by
  apply nodeValid_prime [2, 7, 7549] ⟨211373, 2, [(2, 2), (7, 1), (7549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7549
  · decide +kernel

theorem prime_216967 : Nat.Prime 216967 := by
  apply nodeValid_prime [2, 3, 36161] ⟨216967, 3, [(2, 1), (3, 1), (36161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36161
  · decide +kernel

theorem prime_225263 : Nat.Prime 225263 := by
  apply nodeValid_prime [2, 23, 59, 83] ⟨225263, 5, [(2, 1), (23, 1), (59, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
    · exact prime_83
  · decide +kernel

theorem prime_244493 : Nat.Prime 244493 := by
  apply nodeValid_prime [2, 19, 3217] ⟨244493, 2, [(2, 2), (19, 1), (3217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3217
  · decide +kernel

theorem prime_254071 : Nat.Prime 254071 := by
  apply nodeValid_prime [2, 3, 5, 941] ⟨254071, 3, [(2, 1), (3, 3), (5, 1), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_941
  · decide +kernel

theorem prime_258023 : Nat.Prime 258023 := by
  apply nodeValid_prime [2, 129011] ⟨258023, 5, [(2, 1), (129011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_129011
  · decide +kernel

theorem prime_282559 : Nat.Prime 282559 := by
  apply nodeValid_prime [2, 3, 47093] ⟨282559, 3, [(2, 1), (3, 1), (47093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47093
  · decide +kernel

theorem prime_291491 : Nat.Prime 291491 := by
  apply nodeValid_prime [2, 5, 103, 283] ⟨291491, 2, [(2, 1), (5, 1), (103, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_283
  · decide +kernel

theorem prime_310931 : Nat.Prime 310931 := by
  apply nodeValid_prime [2, 5, 17, 31, 59] ⟨310931, 6, [(2, 1), (5, 1), (17, 1), (31, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_59
  · decide +kernel

theorem prime_315449 : Nat.Prime 315449 := by
  apply nodeValid_prime [2, 7, 43, 131] ⟨315449, 3, [(2, 3), (7, 1), (43, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_131
  · decide +kernel

theorem prime_461093 : Nat.Prime 461093 := by
  apply nodeValid_prime [2, 19, 6067] ⟨461093, 2, [(2, 2), (19, 1), (6067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_6067
  · decide +kernel

theorem prime_467737 : Nat.Prime 467737 := by
  apply nodeValid_prime [2, 3, 19489] ⟨467737, 10, [(2, 3), (3, 1), (19489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19489
  · decide +kernel

theorem prime_470593 : Nat.Prime 470593 := by
  apply nodeValid_prime [2, 3, 19, 43] ⟨470593, 11, [(2, 6), (3, 2), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_630899 : Nat.Prime 630899 := by
  apply nodeValid_prime [2, 315449] ⟨630899, 2, [(2, 1), (315449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_315449
  · decide +kernel

theorem prime_634859 : Nat.Prime 634859 := by
  apply nodeValid_prime [2, 7, 137, 331] ⟨634859, 2, [(2, 1), (7, 1), (137, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_331
  · decide +kernel

theorem prime_722047 : Nat.Prime 722047 := by
  apply nodeValid_prime [2, 3, 13, 9257] ⟨722047, 3, [(2, 1), (3, 1), (13, 1), (9257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_9257
  · decide +kernel

theorem prime_1014397 : Nat.Prime 1014397 := by
  apply nodeValid_prime [2, 3, 84533] ⟨1014397, 5, [(2, 2), (3, 1), (84533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_84533
  · decide +kernel

theorem prime_1325941 : Nat.Prime 1325941 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 41] ⟨1325941, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_1349077 : Nat.Prime 1349077 := by
  apply nodeValid_prime [2, 3, 19, 61, 97] ⟨1349077, 2, [(2, 2), (3, 1), (19, 1), (61, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
    · exact prime_97
  · decide +kernel

theorem prime_1363913 : Nat.Prime 1363913 := by
  apply nodeValid_prime [2, 11, 1409] ⟨1363913, 3, [(2, 3), (11, 2), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1409
  · decide +kernel

theorem prime_1549511 : Nat.Prime 1549511 := by
  apply nodeValid_prime [2, 5, 23, 6737] ⟨1549511, 17, [(2, 1), (5, 1), (23, 1), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_6737
  · decide +kernel

theorem prime_1646299 : Nat.Prime 1646299 := by
  apply nodeValid_prime [2, 3, 43, 709] ⟨1646299, 2, [(2, 1), (3, 3), (43, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_709
  · decide +kernel

theorem prime_1745153 : Nat.Prime 1745153 := by
  apply nodeValid_prime [2, 17, 401] ⟨1745153, 3, [(2, 8), (17, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_401
  · decide +kernel

theorem prime_1865587 : Nat.Prime 1865587 := by
  apply nodeValid_prime [2, 3, 310931] ⟨1865587, 2, [(2, 1), (3, 1), (310931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_310931
  · decide +kernel

theorem prime_2175577 : Nat.Prime 2175577 := by
  apply nodeValid_prime [2, 3, 13, 19, 367] ⟨2175577, 10, [(2, 3), (3, 1), (13, 1), (19, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_367
  · decide +kernel

theorem prime_2825827 : Nat.Prime 2825827 := by
  apply nodeValid_prime [2, 3, 23, 20477] ⟨2825827, 7, [(2, 1), (3, 1), (23, 1), (20477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_20477
  · decide +kernel

theorem prime_3698243 : Nat.Prime 3698243 := by
  apply nodeValid_prime [2, 47, 39343] ⟨3698243, 2, [(2, 1), (47, 1), (39343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_39343
  · decide +kernel

theorem prime_5279623 : Nat.Prime 5279623 := by
  apply nodeValid_prime [2, 3, 17, 191, 271] ⟨5279623, 3, [(2, 1), (3, 1), (17, 1), (191, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_191
    · exact prime_271
  · decide +kernel

theorem prime_6086383 : Nat.Prime 6086383 := by
  apply nodeValid_prime [2, 3, 1014397] ⟨6086383, 5, [(2, 1), (3, 1), (1014397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1014397
  · decide +kernel

theorem prime_6166987 : Nat.Prime 6166987 := by
  apply nodeValid_prime [2, 3, 7, 146833] ⟨6166987, 2, [(2, 1), (3, 1), (7, 1), (146833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_146833
  · decide +kernel

theorem prime_7402237 : Nat.Prime 7402237 := by
  apply nodeValid_prime [2, 3, 157, 3929] ⟨7402237, 2, [(2, 2), (3, 1), (157, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_3929
  · decide +kernel

theorem prime_11666113 : Nat.Prime 11666113 := by
  apply nodeValid_prime [2, 3, 60761] ⟨11666113, 11, [(2, 6), (3, 1), (60761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_60761
  · decide +kernel

theorem prime_13991569 : Nat.Prime 13991569 := by
  apply nodeValid_prime [2, 3, 291491] ⟨13991569, 26, [(2, 4), (3, 1), (291491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_291491
  · decide +kernel

theorem prime_15985163 : Nat.Prime 15985163 := by
  apply nodeValid_prime [2, 41, 151, 1291] ⟨15985163, 2, [(2, 1), (41, 1), (151, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_151
    · exact prime_1291
  · decide +kernel

theorem prime_17524027 : Nat.Prime 17524027 := by
  apply nodeValid_prime [2, 3, 13, 53, 157] ⟨17524027, 2, [(2, 1), (3, 4), (13, 1), (53, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_157
  · decide +kernel

theorem prime_18004319 : Nat.Prime 18004319 := by
  apply nodeValid_prime [2, 661, 13619] ⟨18004319, 7, [(2, 1), (661, 1), (13619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_661
    · exact prime_13619
  · decide +kernel

theorem prime_19126703 : Nat.Prime 19126703 := by
  apply nodeValid_prime [2, 7, 251, 5443] ⟨19126703, 5, [(2, 1), (7, 1), (251, 1), (5443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_251
    · exact prime_5443
  · decide +kernel

theorem prime_23348821 : Nat.Prime 23348821 := by
  apply nodeValid_prime [2, 3, 5, 11, 17, 2081] ⟨23348821, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (17, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_2081
  · decide +kernel

theorem prime_29608949 : Nat.Prime 29608949 := by
  apply nodeValid_prime [2, 7402237] ⟨29608949, 2, [(2, 2), (7402237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7402237
  · decide +kernel

theorem prime_29966609 : Nat.Prime 29966609 := by
  apply nodeValid_prime [2, 7, 23, 11633] ⟨29966609, 6, [(2, 4), (7, 1), (23, 1), (11633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_11633
  · decide +kernel

theorem prime_32543909 : Nat.Prime 32543909 := by
  apply nodeValid_prime [2, 53, 153509] ⟨32543909, 2, [(2, 2), (53, 1), (153509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_153509
  · decide +kernel

theorem prime_32574251 : Nat.Prime 32574251 := by
  apply nodeValid_prime [2, 5, 29, 4493] ⟨32574251, 2, [(2, 1), (5, 3), (29, 1), (4493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_4493
  · decide +kernel

theorem prime_36492607 : Nat.Prime 36492607 := by
  apply nodeValid_prime [2, 3, 225263] ⟨36492607, 13, [(2, 1), (3, 4), (225263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_225263
  · decide +kernel

theorem prime_48657373 : Nat.Prime 48657373 := by
  apply nodeValid_prime [2, 3, 827, 4903] ⟨48657373, 2, [(2, 2), (3, 1), (827, 1), (4903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_827
    · exact prime_4903
  · decide +kernel

theorem prime_56570419 : Nat.Prime 56570419 := by
  apply nodeValid_prime [2, 3, 439, 7159] ⟨56570419, 2, [(2, 1), (3, 2), (439, 1), (7159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_439
    · exact prime_7159
  · decide +kernel

theorem prime_70096109 : Nat.Prime 70096109 := by
  apply nodeValid_prime [2, 17524027] ⟨70096109, 2, [(2, 2), (17524027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17524027
  · decide +kernel

theorem prime_72850159 : Nat.Prime 72850159 := by
  apply nodeValid_prime [2, 3, 1349077] ⟨72850159, 3, [(2, 1), (3, 3), (1349077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1349077
  · decide +kernel

theorem prime_75886289 : Nat.Prime 75886289 := by
  apply nodeValid_prime [2, 487, 9739] ⟨75886289, 3, [(2, 4), (487, 1), (9739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_9739
  · decide +kernel

theorem prime_140192219 : Nat.Prime 140192219 := by
  apply nodeValid_prime [2, 70096109] ⟨140192219, 2, [(2, 1), (70096109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_70096109
  · decide +kernel

theorem prime_166144411 : Nat.Prime 166144411 := by
  apply nodeValid_prime [2, 3, 5, 23, 80263] ⟨166144411, 3, [(2, 1), (3, 2), (5, 1), (23, 1), (80263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_80263
  · decide +kernel

theorem prime_234962317 : Nat.Prime 234962317 := by
  apply nodeValid_prime [2, 3, 2175577] ⟨234962317, 5, [(2, 2), (3, 3), (2175577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2175577
  · decide +kernel

theorem prime_235989673 : Nat.Prime 235989673 := by
  apply nodeValid_prime [2, 3, 307, 32029] ⟨235989673, 7, [(2, 3), (3, 1), (307, 1), (32029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
    · exact prime_32029
  · decide +kernel

theorem prime_239732873 : Nat.Prime 239732873 := by
  apply nodeValid_prime [2, 29966609] ⟨239732873, 3, [(2, 3), (29966609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29966609
  · decide +kernel

theorem prime_279986713 : Nat.Prime 279986713 := by
  apply nodeValid_prime [2, 3, 11666113] ⟨279986713, 5, [(2, 3), (3, 1), (11666113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11666113
  · decide +kernel

theorem prime_280384439 : Nat.Prime 280384439 := by
  apply nodeValid_prime [2, 140192219] ⟨280384439, 11, [(2, 1), (140192219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_140192219
  · decide +kernel

theorem prime_330388301 : Nat.Prime 330388301 := by
  apply nodeValid_prime [2, 5, 11, 29, 10357] ⟨330388301, 2, [(2, 2), (5, 2), (11, 1), (29, 1), (10357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_10357
  · decide +kernel

theorem prime_695811793 : Nat.Prime 695811793 := by
  apply nodeValid_prime [2, 3, 13, 163, 6841] ⟨695811793, 5, [(2, 4), (3, 1), (13, 1), (163, 1), (6841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_163
    · exact prime_6841
  · decide +kernel

theorem prime_722873891 : Nat.Prime 722873891 := by
  apply nodeValid_prime [2, 5, 53, 1363913] ⟨722873891, 2, [(2, 1), (5, 1), (53, 1), (1363913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_1363913
  · decide +kernel

theorem prime_735222737 : Nat.Prime 735222737 := by
  apply nodeValid_prime [2, 6113, 7517] ⟨735222737, 3, [(2, 4), (6113, 1), (7517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6113
    · exact prime_7517
  · decide +kernel

theorem prime_773279497 : Nat.Prime 773279497 := by
  apply nodeValid_prime [2, 3, 11, 761, 1283] ⟨773279497, 5, [(2, 3), (3, 2), (11, 1), (761, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_761
    · exact prime_1283
  · decide +kernel

theorem prime_810199681 : Nat.Prime 810199681 := by
  apply nodeValid_prime [2, 3, 5, 29, 14551] ⟨810199681, 13, [(2, 7), (3, 1), (5, 1), (29, 1), (14551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_14551
  · decide +kernel

theorem prime_1445747783 : Nat.Prime 1445747783 := by
  apply nodeValid_prime [2, 722873891] ⟨1445747783, 5, [(2, 1), (722873891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_722873891
  · decide +kernel

theorem prime_2020174223 : Nat.Prime 2020174223 := by
  apply nodeValid_prime [2, 11, 41, 599, 3739] ⟨2020174223, 5, [(2, 1), (11, 1), (41, 1), (599, 1), (3739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_599
    · exact prime_3739
  · decide +kernel

theorem prime_2865388579 : Nat.Prime 2865388579 := by
  apply nodeValid_prime [2, 3, 13, 2825827] ⟨2865388579, 2, [(2, 1), (3, 1), (13, 2), (2825827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2825827
  · decide +kernel

theorem prime_2891495567 : Nat.Prime 2891495567 := by
  apply nodeValid_prime [2, 1445747783] ⟨2891495567, 5, [(2, 1), (1445747783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1445747783
  · decide +kernel

theorem prime_3401893927 : Nat.Prime 3401893927 := by
  apply nodeValid_prime [2, 3, 179, 401, 2633] ⟨3401893927, 3, [(2, 1), (3, 2), (179, 1), (401, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_401
    · exact prime_2633
  · decide +kernel

theorem prime_4607331067 : Nat.Prime 4607331067 := by
  apply nodeValid_prime [2, 3, 13, 23, 65851] ⟨4607331067, 2, [(2, 1), (3, 2), (13, 2), (23, 1), (65851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_65851
  · decide +kernel

theorem prime_6127382983 : Nat.Prime 6127382983 := by
  apply nodeValid_prime [2, 3, 7, 10139, 14389] ⟨6127382983, 3, [(2, 1), (3, 1), (7, 1), (10139, 1), (14389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10139
    · exact prime_14389
  · decide +kernel

theorem prime_6266183897 : Nat.Prime 6266183897 := by
  apply nodeValid_prime [2, 7, 15985163] ⟨6266183897, 3, [(2, 3), (7, 2), (15985163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15985163
  · decide +kernel

theorem prime_7884209843 : Nat.Prime 7884209843 := by
  apply nodeValid_prime [2, 34261, 115061] ⟨7884209843, 2, [(2, 1), (34261, 1), (115061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_34261
    · exact prime_115061
  · decide +kernel

theorem prime_11420010341 : Nat.Prime 11420010341 := by
  apply nodeValid_prime [2, 5, 29, 2477, 7949] ⟨11420010341, 2, [(2, 2), (5, 1), (29, 1), (2477, 1), (7949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_2477
    · exact prime_7949
  · decide +kernel

theorem prime_14595168103 : Nat.Prime 14595168103 := by
  apply nodeValid_prime [2, 3, 43, 56570419] ⟨14595168103, 6, [(2, 1), (3, 1), (43, 1), (56570419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_56570419
  · decide +kernel

theorem prime_16392017819 : Nat.Prime 16392017819 := by
  apply nodeValid_prime [2, 11, 1181, 630899] ⟨16392017819, 2, [(2, 1), (11, 1), (1181, 1), (630899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1181
    · exact prime_630899
  · decide +kernel

theorem prime_23627338807 : Nat.Prime 23627338807 := by
  apply nodeValid_prime [2, 3, 647, 6086383] ⟨23627338807, 5, [(2, 1), (3, 1), (647, 1), (6086383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_647
    · exact prime_6086383
  · decide +kernel

theorem prime_29167188517 : Nat.Prime 29167188517 := by
  apply nodeValid_prime [2, 3, 810199681] ⟨29167188517, 2, [(2, 2), (3, 2), (810199681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_810199681
  · decide +kernel

theorem prime_35669047943 : Nat.Prime 35669047943 := by
  apply nodeValid_prime [2, 11, 499, 743, 4373] ⟨35669047943, 5, [(2, 1), (11, 1), (499, 1), (743, 1), (4373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_499
    · exact prime_743
    · exact prime_4373
  · decide +kernel

theorem prime_48290939261 : Nat.Prime 48290939261 := by
  apply nodeValid_prime [2, 5, 109, 1171, 18917] ⟨48290939261, 2, [(2, 2), (5, 1), (109, 1), (1171, 1), (18917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_1171
    · exact prime_18917
  · decide +kernel

theorem prime_54087976759 : Nat.Prime 54087976759 := by
  apply nodeValid_prime [2, 3, 277, 32543909] ⟨54087976759, 3, [(2, 1), (3, 1), (277, 1), (32543909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_32543909
  · decide +kernel

theorem prime_71338095887 : Nat.Prime 71338095887 := by
  apply nodeValid_prime [2, 35669047943] ⟨71338095887, 5, [(2, 1), (35669047943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35669047943
  · decide +kernel

theorem prime_76378751387 : Nat.Prime 76378751387 := by
  apply nodeValid_prime [2, 7, 37, 4679, 31513] ⟨76378751387, 5, [(2, 1), (7, 1), (37, 1), (4679, 1), (31513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_4679
    · exact prime_31513
  · decide +kernel

theorem prime_82965538699 : Nat.Prime 82965538699 := by
  apply nodeValid_prime [2, 3, 7, 6991, 282559] ⟨82965538699, 2, [(2, 1), (3, 1), (7, 1), (6991, 1), (282559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6991
    · exact prime_282559
  · decide +kernel

theorem prime_84218656141 : Nat.Prime 84218656141 := by
  apply nodeValid_prime [2, 3, 5, 21383, 21881] ⟨84218656141, 26, [(2, 2), (3, 2), (5, 1), (21383, 1), (21881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21383
    · exact prime_21881
  · decide +kernel

theorem prime_93633715937 : Nat.Prime 93633715937 := by
  apply nodeValid_prime [2, 89, 743, 44249] ⟨93633715937, 3, [(2, 5), (89, 1), (743, 1), (44249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_743
    · exact prime_44249
  · decide +kernel

theorem prime_103595083811 : Nat.Prime 103595083811 := by
  apply nodeValid_prime [2, 5, 37, 279986713] ⟨103595083811, 2, [(2, 1), (5, 1), (37, 1), (279986713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_279986713
  · decide +kernel

theorem prime_132061071719 : Nat.Prime 132061071719 := by
  apply nodeValid_prime [2, 19, 2621, 1325941] ⟨132061071719, 11, [(2, 1), (19, 1), (2621, 1), (1325941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2621
    · exact prime_1325941
  · decide +kernel

theorem prime_155061563869 : Nat.Prime 155061563869 := by
  apply nodeValid_prime [2, 3, 5651, 254071] ⟨155061563869, 2, [(2, 2), (3, 3), (5651, 1), (254071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5651
    · exact prime_254071
  · decide +kernel

theorem prime_183702272059 : Nat.Prime 183702272059 := by
  apply nodeValid_prime [2, 3, 3401893927] ⟨183702272059, 2, [(2, 1), (3, 3), (3401893927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3401893927
  · decide +kernel

theorem prime_228400206821 : Nat.Prime 228400206821 := by
  apply nodeValid_prime [2, 5, 11420010341] ⟨228400206821, 2, [(2, 2), (5, 1), (11420010341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11420010341
  · decide +kernel

theorem prime_230859939419 : Nat.Prime 230859939419 := by
  apply nodeValid_prime [2, 157, 735222737] ⟨230859939419, 2, [(2, 1), (157, 1), (735222737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_735222737
  · decide +kernel

theorem prime_915562938623 : Nat.Prime 915562938623 := by
  apply nodeValid_prime [2, 61, 673, 1697, 6571] ⟨915562938623, 5, [(2, 1), (61, 1), (673, 1), (1697, 1), (6571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_673
    · exact prime_1697
    · exact prime_6571
  · decide +kernel

theorem prime_932355785423 : Nat.Prime 932355785423 := by
  apply nodeValid_prime [2, 17, 83, 330388301] ⟨932355785423, 5, [(2, 1), (17, 1), (83, 1), (330388301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_83
    · exact prime_330388301
  · decide +kernel

theorem prime_933350032943 : Nat.Prime 933350032943 := by
  apply nodeValid_prime [2, 37, 59671, 211373] ⟨933350032943, 5, [(2, 1), (37, 1), (59671, 1), (211373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_59671
    · exact prime_211373
  · decide +kernel

theorem prime_1825241848709 : Nat.Prime 1825241848709 := by
  apply nodeValid_prime [2, 73, 1031, 1667, 3637] ⟨1825241848709, 2, [(2, 2), (73, 1), (1031, 1), (1667, 1), (3637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1031
    · exact prime_1667
    · exact prime_3637
  · decide +kernel

theorem prime_1825241851379 : Nat.Prime 1825241851379 := by
  apply nodeValid_prime [2, 11, 82965538699] ⟨1825241851379, 2, [(2, 1), (11, 1), (82965538699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_82965538699
  · decide +kernel

theorem prime_1825241851583 : Nat.Prime 1825241851583 := by
  apply nodeValid_prime [2, 173, 293, 18004319] ⟨1825241851583, 5, [(2, 1), (173, 1), (293, 1), (18004319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_293
    · exact prime_18004319
  · decide +kernel

theorem prime_1827201654569 : Nat.Prime 1827201654569 := by
  apply nodeValid_prime [2, 228400206821] ⟨1827201654569, 3, [(2, 3), (228400206821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_228400206821
  · decide +kernel

theorem prime_1827201654799 : Nat.Prime 1827201654799 := by
  apply nodeValid_prime [2, 3, 13, 36899, 634859] ⟨1827201654799, 3, [(2, 1), (3, 1), (13, 1), (36899, 1), (634859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_36899
    · exact prime_634859
  · decide +kernel

theorem prime_1827201768419 : Nat.Prime 1827201768419 := by
  apply nodeValid_prime [2, 13, 101, 695811793] ⟨1827201768419, 2, [(2, 1), (13, 1), (101, 1), (695811793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_101
    · exact prime_695811793
  · decide +kernel

theorem prime_1829163110057 : Nat.Prime 1829163110057 := by
  apply nodeValid_prime [2, 23, 131, 75886289] ⟨1829163110057, 3, [(2, 3), (23, 1), (131, 1), (75886289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_131
    · exact prime_75886289
  · decide +kernel

theorem prime_1829163113677 : Nat.Prime 1829163113677 := by
  apply nodeValid_prime [2, 3, 71, 523, 456109] ⟨1829163113677, 2, [(2, 2), (3, 3), (71, 1), (523, 1), (456109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_523
    · exact prime_456109
  · decide +kernel

theorem prime_1829163114703 : Nat.Prime 1829163114703 := by
  apply nodeValid_prime [2, 3, 7, 11, 23, 19126703] ⟨1829163114703, 5, [(2, 1), (3, 3), (7, 1), (11, 1), (23, 1), (19126703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_19126703
  · decide +kernel

theorem prime_1831125848897 : Nat.Prime 1831125848897 := by
  apply nodeValid_prime [2, 37, 773279497] ⟨1831125848897, 3, [(2, 6), (37, 1), (773279497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_773279497
  · decide +kernel

theorem prime_1831125849563 : Nat.Prime 1831125849563 := by
  apply nodeValid_prime [2, 37, 6691, 3698243] ⟨1831125849563, 2, [(2, 1), (37, 1), (6691, 1), (3698243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_6691
    · exact prime_3698243
  · decide +kernel

theorem prime_1831125877247 : Nat.Prime 1831125877247 := by
  apply nodeValid_prime [2, 915562938623] ⟨1831125877247, 5, [(2, 1), (915562938623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_915562938623
  · decide +kernel

theorem prime_1833090032591 : Nat.Prime 1833090032591 := by
  apply nodeValid_prime [2, 5, 41, 151, 29608949] ⟨1833090032591, 11, [(2, 1), (5, 1), (41, 1), (151, 1), (29608949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_151
    · exact prime_29608949
  · decide +kernel

theorem prime_1833090033289 : Nat.Prime 1833090033289 := by
  apply nodeValid_prime [2, 3, 76378751387] ⟨1833090033289, 17, [(2, 3), (3, 1), (76378751387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_76378751387
  · decide +kernel

theorem prime_1833090070061 : Nat.Prime 1833090070061 := by
  apply nodeValid_prime [2, 5, 19, 24133, 199889] ⟨1833090070061, 2, [(2, 2), (5, 1), (19, 1), (24133, 1), (199889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_24133
    · exact prime_199889
  · decide +kernel

theorem prime_1835055691919 : Nat.Prime 1835055691919 := by
  apply nodeValid_prime [2, 19, 48290939261] ⟨1835055691919, 7, [(2, 1), (19, 1), (48290939261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_48290939261
  · decide +kernel

theorem prime_1835055695771 : Nat.Prime 1835055695771 := by
  apply nodeValid_prime [2, 5, 11, 71, 234962317] ⟨1835055695771, 6, [(2, 1), (5, 1), (11, 1), (71, 1), (234962317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_71
    · exact prime_234962317
  · decide +kernel

theorem prime_1835055697249 : Nat.Prime 1835055697249 := by
  apply nodeValid_prime [2, 3, 235989673] ⟨1835055697249, 7, [(2, 5), (3, 5), (235989673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_235989673
  · decide +kernel

theorem prime_1837022720591 : Nat.Prime 1837022720591 := by
  apply nodeValid_prime [2, 5, 183702272059] ⟨1837022720591, 7, [(2, 1), (5, 1), (183702272059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_183702272059
  · decide +kernel

theorem prime_1837022739151 : Nat.Prime 1837022739151 := by
  apply nodeValid_prime [2, 3, 5, 43, 173, 1646299] ⟨1837022739151, 6, [(2, 1), (3, 1), (5, 2), (43, 1), (173, 1), (1646299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_173
    · exact prime_1646299
  · decide +kernel

theorem prime_1838991180613 : Nat.Prime 1838991180613 := by
  apply nodeValid_prime [2, 3, 53, 2891495567] ⟨1838991180613, 6, [(2, 2), (3, 1), (53, 1), (2891495567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_2891495567
  · decide +kernel

theorem prime_1838991180979 : Nat.Prime 1838991180979 := by
  apply nodeValid_prime [2, 3, 7, 14595168103] ⟨1838991180979, 2, [(2, 1), (3, 2), (7, 1), (14595168103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14595168103
  · decide +kernel

theorem prime_1838991209807 : Nat.Prime 1838991209807 := by
  apply nodeValid_prime [2, 17, 54087976759] ⟨1838991209807, 5, [(2, 1), (17, 1), (54087976759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_54087976759
  · decide +kernel

theorem prime_1840961102597 : Nat.Prime 1840961102597 := by
  apply nodeValid_prime [2, 7, 11, 233, 1549, 16561] ⟨1840961102597, 2, [(2, 2), (7, 1), (11, 1), (233, 1), (1549, 1), (16561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_233
    · exact prime_1549
    · exact prime_16561
  · decide +kernel

theorem prime_1840961140331 : Nat.Prime 1840961140331 := by
  apply nodeValid_prime [2, 5, 13, 23, 449, 59621] ⟨1840961140331, 2, [(2, 1), (5, 1), (13, 1), (23, 2), (449, 1), (59621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_449
    · exact prime_59621
  · decide +kernel

theorem prime_1840961140567 : Nat.Prime 1840961140567 := by
  apply nodeValid_prime [2, 3, 17, 773, 23348821] ⟨1840961140567, 6, [(2, 1), (3, 1), (17, 1), (773, 1), (23348821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_773
    · exact prime_23348821
  · decide +kernel

theorem prime_1842932424649 : Nat.Prime 1842932424649 := by
  apply nodeValid_prime [2, 3, 7, 47, 499, 467737] ⟨1842932424649, 23, [(2, 3), (3, 1), (7, 1), (47, 1), (499, 1), (467737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_499
    · exact prime_467737
  · decide +kernel

theorem prime_1842932426801 : Nat.Prime 1842932426801 := by
  apply nodeValid_prime [2, 5, 4607331067] ⟨1842932426801, 6, [(2, 4), (5, 2), (4607331067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4607331067
  · decide +kernel

theorem prime_1842932426947 : Nat.Prime 1842932426947 := by
  apply nodeValid_prime [2, 3, 13, 23627338807] ⟨1842932426947, 2, [(2, 1), (3, 1), (13, 1), (23627338807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23627338807
  · decide +kernel

theorem prime_1844905102519 : Nat.Prime 1844905102519 := by
  apply nodeValid_prime [2, 3, 43, 3833, 1865587] ⟨1844905102519, 3, [(2, 1), (3, 1), (43, 1), (3833, 1), (1865587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_3833
    · exact prime_1865587
  · decide +kernel

theorem prime_1844905103263 : Nat.Prime 1844905103263 := by
  apply nodeValid_prime [2, 3, 13, 7884209843] ⟨1844905103263, 3, [(2, 1), (3, 2), (13, 1), (7884209843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_7884209843
  · decide +kernel

theorem prime_1844905177889 : Nat.Prime 1844905177889 := by
  apply nodeValid_prime [2, 79847, 722047] ⟨1844905177889, 3, [(2, 5), (79847, 1), (722047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79847
    · exact prime_722047
  · decide +kernel

theorem prime_1846879366883 : Nat.Prime 1846879366883 := by
  apply nodeValid_prime [2, 11, 643, 887, 13381] ⟨1846879366883, 2, [(2, 1), (11, 2), (643, 1), (887, 1), (13381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_643
    · exact prime_887
    · exact prime_13381
  · decide +kernel

theorem prime_1846879515353 : Nat.Prime 1846879515353 := by
  apply nodeValid_prime [2, 230859939419] ⟨1846879515353, 3, [(2, 3), (230859939419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_230859939419
  · decide +kernel

theorem prime_1846879515421 : Nat.Prime 1846879515421 := by
  apply nodeValid_prime [2, 3, 5, 141871, 216967] ⟨1846879515421, 6, [(2, 2), (3, 1), (5, 1), (141871, 1), (216967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_141871
    · exact prime_216967
  · decide +kernel

theorem prime_1848854990767 : Nat.Prime 1848854990767 := by
  apply nodeValid_prime [2, 3, 7, 157, 280384439] ⟨1848854990767, 3, [(2, 1), (3, 1), (7, 1), (157, 1), (280384439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
    · exact prime_280384439
  · decide +kernel

theorem prime_1848855004067 : Nat.Prime 1848855004067 := by
  apply nodeValid_prime [2, 7, 132061071719] ⟨1848855004067, 2, [(2, 1), (7, 1), (132061071719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_132061071719
  · decide +kernel

theorem prime_1848855005609 : Nat.Prime 1848855005609 := by
  apply nodeValid_prime [2, 13, 107, 166144411] ⟨1848855005609, 3, [(2, 3), (13, 1), (107, 1), (166144411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_107
    · exact prime_166144411
  · decide +kernel

theorem prime_1850832008083 : Nat.Prime 1850832008083 := by
  apply nodeValid_prime [2, 3, 66359, 1549511] ⟨1850832008083, 2, [(2, 1), (3, 2), (66359, 1), (1549511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66359
    · exact prime_1549511
  · decide +kernel

theorem prime_1850832015103 : Nat.Prime 1850832015103 := by
  apply nodeValid_prime [2, 3, 7, 389, 1087, 34739] ⟨1850832015103, 3, [(2, 1), (3, 2), (7, 1), (389, 1), (1087, 1), (34739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_389
    · exact prime_1087
    · exact prime_34739
  · decide +kernel

theorem prime_1850832041827 : Nat.Prime 1850832041827 := by
  apply nodeValid_prime [2, 3, 79, 107, 36492607] ⟨1850832041827, 5, [(2, 1), (3, 1), (79, 1), (107, 1), (36492607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_107
    · exact prime_36492607
  · decide +kernel

theorem prime_1852810433783 : Nat.Prime 1852810433783 := by
  apply nodeValid_prime [2, 7, 11, 17, 29, 2621, 9311] ⟨1852810433783, 5, [(2, 1), (7, 1), (11, 1), (17, 1), (29, 1), (2621, 1), (9311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_29
    · exact prime_2621
    · exact prime_9311
  · decide +kernel

theorem prime_1852810435103 : Nat.Prime 1852810435103 := by
  apply nodeValid_prime [2, 11, 84218656141] ⟨1852810435103, 5, [(2, 1), (11, 1), (84218656141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_84218656141
  · decide +kernel

theorem prime_1852810526309 : Nat.Prime 1852810526309 := by
  apply nodeValid_prime [2, 7, 337, 761, 258023] ⟨1852810526309, 2, [(2, 2), (7, 1), (337, 1), (761, 1), (258023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_337
    · exact prime_761
    · exact prime_258023
  · decide +kernel

theorem prime_1854790433513 : Nat.Prime 1854790433513 := by
  apply nodeValid_prime [2, 37, 6266183897] ⟨1854790433513, 3, [(2, 3), (37, 1), (6266183897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_6266183897
  · decide +kernel

theorem prime_1854790492073 : Nat.Prime 1854790492073 := by
  apply nodeValid_prime [2, 7, 18979, 1745153] ⟨1854790492073, 3, [(2, 3), (7, 1), (18979, 1), (1745153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_18979
    · exact prime_1745153
  · decide +kernel

theorem prime_1854790493063 : Nat.Prime 1854790493063 := by
  apply nodeValid_prime [2, 13, 71338095887] ⟨1854790493063, 5, [(2, 1), (13, 1), (71338095887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71338095887
  · decide +kernel

theorem prime_1856771771369 : Nat.Prime 1856771771369 := by
  apply nodeValid_prime [2, 17, 19, 2939, 244493] ⟨1856771771369, 3, [(2, 3), (17, 1), (19, 1), (2939, 1), (244493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_2939
    · exact prime_244493
  · decide +kernel

theorem prime_1856771799193 : Nat.Prime 1856771799193 := by
  apply nodeValid_prime [2, 3, 2865388579] ⟨1856771799193, 10, [(2, 3), (3, 4), (2865388579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2865388579
  · decide +kernel

theorem prime_1856771799373 : Nat.Prime 1856771799373 := by
  apply nodeValid_prime [2, 3, 7, 113, 997, 9343] ⟨1856771799373, 2, [(2, 2), (3, 2), (7, 2), (113, 1), (997, 1), (9343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
    · exact prime_997
    · exact prime_9343
  · decide +kernel

theorem prime_1858754549749 : Nat.Prime 1858754549749 := by
  apply nodeValid_prime [2, 3, 25117, 6166987] ⟨1858754549749, 2, [(2, 2), (3, 1), (25117, 1), (6166987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25117
    · exact prime_6166987
  · decide +kernel

theorem prime_1858754632411 : Nat.Prime 1858754632411 := by
  apply nodeValid_prime [2, 3, 5, 13, 71, 181, 683] ⟨1858754632411, 2, [(2, 1), (3, 2), (5, 1), (13, 1), (71, 1), (181, 2), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_71
    · exact prime_181
    · exact prime_683
  · decide +kernel

theorem prime_1858754632627 : Nat.Prime 1858754632627 := by
  apply nodeValid_prime [2, 3, 19559, 5279623] ⟨1858754632627, 5, [(2, 1), (3, 2), (19559, 1), (5279623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19559
    · exact prime_5279623
  · decide +kernel

theorem prime_1860738761179 : Nat.Prime 1860738761179 := by
  apply nodeValid_prime [2, 3, 11, 43, 72850159] ⟨1860738761179, 2, [(2, 1), (3, 3), (11, 1), (43, 1), (72850159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_72850159
  · decide +kernel

theorem prime_1860738761311 : Nat.Prime 1860738761311 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 31, 13991569] ⟨1860738761311, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (31, 1), (13991569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_13991569
  · decide +kernel

theorem prime_1860738766429 : Nat.Prime 1860738766429 := by
  apply nodeValid_prime [2, 3, 155061563869] ⟨1860738766429, 17, [(2, 2), (3, 1), (155061563869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_155061563869
  · decide +kernel

theorem prime_1862724423211 : Nat.Prime 1862724423211 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 239732873] ⟨1862724423211, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (239732873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_239732873
  · decide +kernel

theorem prime_1862724423587 : Nat.Prime 1862724423587 := by
  apply nodeValid_prime [2, 13, 155377, 461093] ⟨1862724423587, 2, [(2, 1), (13, 1), (155377, 1), (461093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_155377
    · exact prime_461093
  · decide +kernel

theorem prime_1862724426833 : Nat.Prime 1862724426833 := by
  apply nodeValid_prime [2, 19, 6127382983] ⟨1862724426833, 3, [(2, 4), (19, 1), (6127382983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_6127382983
  · decide +kernel

theorem prime_1864711508599 : Nat.Prime 1864711508599 := by
  apply nodeValid_prime [2, 3, 103595083811] ⟨1864711508599, 3, [(2, 1), (3, 2), (103595083811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103595083811
  · decide +kernel

theorem prime_1864711569719 : Nat.Prime 1864711569719 := by
  apply nodeValid_prime [2, 941, 7549, 131251] ⟨1864711569719, 11, [(2, 1), (941, 1), (7549, 1), (131251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_941
    · exact prime_7549
    · exact prime_131251
  · decide +kernel

theorem prime_1864711570847 : Nat.Prime 1864711570847 := by
  apply nodeValid_prime [2, 932355785423] ⟨1864711570847, 5, [(2, 1), (932355785423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_932355785423
  · decide +kernel

theorem prime_1866700027807 : Nat.Prime 1866700027807 := by
  apply nodeValid_prime [2, 3, 9551, 32574251] ⟨1866700027807, 3, [(2, 1), (3, 1), (9551, 1), (32574251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9551
    · exact prime_32574251
  · decide +kernel

theorem prime_1866700065089 : Nat.Prime 1866700065089 := by
  apply nodeValid_prime [2, 29167188517] ⟨1866700065089, 3, [(2, 6), (29167188517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29167188517
  · decide +kernel

theorem prime_1866700065887 : Nat.Prime 1866700065887 := by
  apply nodeValid_prime [2, 933350032943] ⟨1866700065887, 5, [(2, 1), (933350032943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_933350032943
  · decide +kernel

theorem prime_1868689979119 : Nat.Prime 1868689979119 := by
  apply nodeValid_prime [2, 3, 167, 1321, 470593] ⟨1868689979119, 6, [(2, 1), (3, 2), (167, 1), (1321, 1), (470593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_1321
    · exact prime_470593
  · decide +kernel

theorem prime_1868690031337 : Nat.Prime 1868690031337 := by
  apply nodeValid_prime [2, 3, 82567, 314339] ⟨1868690031337, 7, [(2, 3), (3, 2), (82567, 1), (314339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_82567
    · exact prime_314339
  · decide +kernel

theorem prime_1868690031367 : Nat.Prime 1868690031367 := by
  apply nodeValid_prime [2, 3, 19, 16392017819] ⟨1868690031367, 3, [(2, 1), (3, 1), (19, 1), (16392017819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_16392017819
  · decide +kernel

theorem prime_1870681329971 : Nat.Prime 1870681329971 := by
  apply nodeValid_prime [2, 5, 3617, 6367, 8123] ⟨1870681329971, 2, [(2, 1), (5, 1), (3617, 1), (6367, 1), (8123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3617
    · exact prime_6367
    · exact prime_8123
  · decide +kernel

theorem prime_1870681330499 : Nat.Prime 1870681330499 := by
  apply nodeValid_prime [2, 463, 2020174223] ⟨1870681330499, 2, [(2, 1), (463, 1), (2020174223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_463
    · exact prime_2020174223
  · decide +kernel

theorem prime_1870681362359 : Nat.Prime 1870681362359 := by
  apply nodeValid_prime [2, 47, 409, 48657373] ⟨1870681362359, 19, [(2, 1), (47, 1), (409, 1), (48657373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_409
    · exact prime_48657373
  · decide +kernel

theorem prime_1872674187001 : Nat.Prime 1872674187001 := by
  apply nodeValid_prime [2, 3, 5, 67, 89, 104683] ⟨1872674187001, 11, [(2, 3), (3, 1), (5, 3), (67, 1), (89, 1), (104683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_89
    · exact prime_104683
  · decide +kernel

theorem prime_1872674318549 : Nat.Prime 1872674318549 := by
  apply nodeValid_prime [2, 11, 887, 4019, 11939] ⟨1872674318549, 2, [(2, 2), (11, 1), (887, 1), (4019, 1), (11939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_887
    · exact prime_4019
    · exact prime_11939
  · decide +kernel

theorem prime_1872674318741 : Nat.Prime 1872674318741 := by
  apply nodeValid_prime [2, 5, 93633715937] ⟨1872674318741, 2, [(2, 2), (5, 1), (93633715937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_93633715937
  · decide +kernel

end Sude.Lucas.Generated
