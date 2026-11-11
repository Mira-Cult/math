import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0070

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4549 : Nat.Prime 4549 := by
  apply nodeValid_prime [2, 3, 379] ⟨4549, 6, [(2, 2), (3, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
  · decide +kernel

theorem prime_7187 : Nat.Prime 7187 := by
  apply nodeValid_prime [2, 3593] ⟨7187, 2, [(2, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3593
  · decide +kernel

theorem prime_8887 : Nat.Prime 8887 := by
  apply nodeValid_prime [2, 3, 1481] ⟨8887, 3, [(2, 1), (3, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1481
  · decide +kernel

theorem prime_9319 : Nat.Prime 9319 := by
  apply nodeValid_prime [2, 3, 1553] ⟨9319, 3, [(2, 1), (3, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1553
  · decide +kernel

theorem prime_9343 : Nat.Prime 9343 := by
  apply nodeValid_prime [2, 3, 173] ⟨9343, 5, [(2, 1), (3, 3), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
  · decide +kernel

theorem prime_15809 : Nat.Prime 15809 := by
  apply nodeValid_prime [2, 13, 19] ⟨15809, 3, [(2, 6), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_17959 : Nat.Prime 17959 := by
  apply nodeValid_prime [2, 3, 41, 73] ⟨17959, 6, [(2, 1), (3, 1), (41, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_73
  · decide +kernel

theorem prime_18757 : Nat.Prime 18757 := by
  apply nodeValid_prime [2, 3, 521] ⟨18757, 2, [(2, 2), (3, 2), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
  · decide +kernel

theorem prime_19001 : Nat.Prime 19001 := by
  apply nodeValid_prime [2, 5, 19] ⟨19001, 3, [(2, 3), (5, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_22727 : Nat.Prime 22727 := by
  apply nodeValid_prime [2, 11, 1033] ⟨22727, 5, [(2, 1), (11, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1033
  · decide +kernel

theorem prime_23977 : Nat.Prime 23977 := by
  apply nodeValid_prime [2, 3, 37] ⟨23977, 5, [(2, 3), (3, 4), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_26387 : Nat.Prime 26387 := by
  apply nodeValid_prime [2, 79, 167] ⟨26387, 2, [(2, 1), (79, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_167
  · decide +kernel

theorem prime_27407 : Nat.Prime 27407 := by
  apply nodeValid_prime [2, 71, 193] ⟨27407, 5, [(2, 1), (71, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_193
  · decide +kernel

theorem prime_27851 : Nat.Prime 27851 := by
  apply nodeValid_prime [2, 5, 557] ⟨27851, 2, [(2, 1), (5, 2), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_557
  · decide +kernel

theorem prime_28729 : Nat.Prime 28729 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨28729, 22, [(2, 3), (3, 3), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_31277 : Nat.Prime 31277 := by
  apply nodeValid_prime [2, 7, 1117] ⟨31277, 2, [(2, 2), (7, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1117
  · decide +kernel

theorem prime_32381 : Nat.Prime 32381 := by
  apply nodeValid_prime [2, 5, 1619] ⟨32381, 2, [(2, 2), (5, 1), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1619
  · decide +kernel

theorem prime_35993 : Nat.Prime 35993 := by
  apply nodeValid_prime [2, 11, 409] ⟨35993, 3, [(2, 3), (11, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_409
  · decide +kernel

theorem prime_40507 : Nat.Prime 40507 := by
  apply nodeValid_prime [2, 3, 43, 157] ⟨40507, 2, [(2, 1), (3, 1), (43, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_157
  · decide +kernel

theorem prime_42929 : Nat.Prime 42929 := by
  apply nodeValid_prime [2, 2683] ⟨42929, 3, [(2, 4), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2683
  · decide +kernel

theorem prime_46457 : Nat.Prime 46457 := by
  apply nodeValid_prime [2, 5807] ⟨46457, 3, [(2, 3), (5807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5807
  · decide +kernel

theorem prime_50333 : Nat.Prime 50333 := by
  apply nodeValid_prime [2, 12583] ⟨50333, 2, [(2, 2), (12583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12583
  · decide +kernel

theorem prime_57947 : Nat.Prime 57947 := by
  apply nodeValid_prime [2, 7, 4139] ⟨57947, 5, [(2, 1), (7, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4139
  · decide +kernel

theorem prime_61253 : Nat.Prime 61253 := by
  apply nodeValid_prime [2, 15313] ⟨61253, 2, [(2, 2), (15313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15313
  · decide +kernel

theorem prime_65111 : Nat.Prime 65111 := by
  apply nodeValid_prime [2, 5, 17, 383] ⟨65111, 7, [(2, 1), (5, 1), (17, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_383
  · decide +kernel

theorem prime_68209 : Nat.Prime 68209 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨68209, 13, [(2, 4), (3, 1), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_71987 : Nat.Prime 71987 := by
  apply nodeValid_prime [2, 35993] ⟨71987, 2, [(2, 1), (35993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35993
  · decide +kernel

theorem prime_79259 : Nat.Prime 79259 := by
  apply nodeValid_prime [2, 23, 1723] ⟨79259, 2, [(2, 1), (23, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1723
  · decide +kernel

theorem prime_82591 : Nat.Prime 82591 := by
  apply nodeValid_prime [2, 3, 5, 2753] ⟨82591, 6, [(2, 1), (3, 1), (5, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2753
  · decide +kernel

theorem prime_94949 : Nat.Prime 94949 := by
  apply nodeValid_prime [2, 7, 3391] ⟨94949, 2, [(2, 2), (7, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3391
  · decide +kernel

theorem prime_103393 : Nat.Prime 103393 := by
  apply nodeValid_prime [2, 3, 359] ⟨103393, 5, [(2, 5), (3, 2), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
  · decide +kernel

theorem prime_113213 : Nat.Prime 113213 := by
  apply nodeValid_prime [2, 11, 31, 83] ⟨113213, 2, [(2, 2), (11, 1), (31, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_83
  · decide +kernel

theorem prime_120349 : Nat.Prime 120349 := by
  apply nodeValid_prime [2, 3, 3343] ⟨120349, 6, [(2, 2), (3, 2), (3343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3343
  · decide +kernel

theorem prime_134923 : Nat.Prime 134923 := by
  apply nodeValid_prime [2, 3, 113, 199] ⟨134923, 2, [(2, 1), (3, 1), (113, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_199
  · decide +kernel

theorem prime_140111 : Nat.Prime 140111 := by
  apply nodeValid_prime [2, 5, 14011] ⟨140111, 11, [(2, 1), (5, 1), (14011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14011
  · decide +kernel

theorem prime_167107 : Nat.Prime 167107 := by
  apply nodeValid_prime [2, 3, 27851] ⟨167107, 3, [(2, 1), (3, 1), (27851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27851
  · decide +kernel

theorem prime_171473 : Nat.Prime 171473 := by
  apply nodeValid_prime [2, 7, 1531] ⟨171473, 3, [(2, 4), (7, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1531
  · decide +kernel

theorem prime_179591 : Nat.Prime 179591 := by
  apply nodeValid_prime [2, 5, 17959] ⟨179591, 11, [(2, 1), (5, 1), (17959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17959
  · decide +kernel

theorem prime_226427 : Nat.Prime 226427 := by
  apply nodeValid_prime [2, 113213] ⟨226427, 2, [(2, 1), (113213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_113213
  · decide +kernel

theorem prime_254281 : Nat.Prime 254281 := by
  apply nodeValid_prime [2, 3, 5, 13, 163] ⟨254281, 7, [(2, 3), (3, 1), (5, 1), (13, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_163
  · decide +kernel

theorem prime_266051 : Nat.Prime 266051 := by
  apply nodeValid_prime [2, 5, 17, 313] ⟨266051, 2, [(2, 1), (5, 2), (17, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_313
  · decide +kernel

theorem prime_294821 : Nat.Prime 294821 := by
  apply nodeValid_prime [2, 5, 14741] ⟨294821, 2, [(2, 2), (5, 1), (14741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14741
  · decide +kernel

theorem prime_348077 : Nat.Prime 348077 := by
  apply nodeValid_prime [2, 173, 503] ⟨348077, 2, [(2, 2), (173, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_503
  · decide +kernel

theorem prime_454541 : Nat.Prime 454541 := by
  apply nodeValid_prime [2, 5, 22727] ⟨454541, 2, [(2, 2), (5, 1), (22727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22727
  · decide +kernel

theorem prime_487463 : Nat.Prime 487463 := by
  apply nodeValid_prime [2, 23, 10597] ⟨487463, 5, [(2, 1), (23, 1), (10597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_10597
  · decide +kernel

theorem prime_496841 : Nat.Prime 496841 := by
  apply nodeValid_prime [2, 5, 12421] ⟨496841, 3, [(2, 3), (5, 1), (12421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12421
  · decide +kernel

theorem prime_568907 : Nat.Prime 568907 := by
  apply nodeValid_prime [2, 13, 21881] ⟨568907, 2, [(2, 1), (13, 1), (21881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_21881
  · decide +kernel

theorem prime_587849 : Nat.Prime 587849 := by
  apply nodeValid_prime [2, 197, 373] ⟨587849, 3, [(2, 3), (197, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_373
  · decide +kernel

theorem prime_598729 : Nat.Prime 598729 := by
  apply nodeValid_prime [2, 3, 13, 19, 101] ⟨598729, 14, [(2, 3), (3, 1), (13, 1), (19, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_101
  · decide +kernel

theorem prime_627059 : Nat.Prime 627059 := by
  apply nodeValid_prime [2, 157, 1997] ⟨627059, 2, [(2, 1), (157, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_1997
  · decide +kernel

theorem prime_632447 : Nat.Prime 632447 := by
  apply nodeValid_prime [2, 316223] ⟨632447, 5, [(2, 1), (316223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_316223
  · decide +kernel

theorem prime_696119 : Nat.Prime 696119 := by
  apply nodeValid_prime [2, 23, 37, 409] ⟨696119, 7, [(2, 1), (23, 1), (37, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_409
  · decide +kernel

theorem prime_737657 : Nat.Prime 737657 := by
  apply nodeValid_prime [2, 19, 23, 211] ⟨737657, 3, [(2, 3), (19, 1), (23, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_211
  · decide +kernel

theorem prime_818509 : Nat.Prime 818509 := by
  apply nodeValid_prime [2, 3, 68209] ⟨818509, 2, [(2, 2), (3, 1), (68209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_68209
  · decide +kernel

theorem prime_993683 : Nat.Prime 993683 := by
  apply nodeValid_prime [2, 496841] ⟨993683, 2, [(2, 1), (496841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_496841
  · decide +kernel

theorem prime_1254119 : Nat.Prime 1254119 := by
  apply nodeValid_prime [2, 627059] ⟨1254119, 11, [(2, 1), (627059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_627059
  · decide +kernel

theorem prime_1377107 : Nat.Prime 1377107 := by
  apply nodeValid_prime [2, 109, 6317] ⟨1377107, 2, [(2, 1), (109, 1), (6317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_6317
  · decide +kernel

theorem prime_1380779 : Nat.Prime 1380779 := by
  apply nodeValid_prime [2, 7, 98627] ⟨1380779, 2, [(2, 1), (7, 1), (98627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_98627
  · decide +kernel

theorem prime_1390729 : Nat.Prime 1390729 := by
  apply nodeValid_prime [2, 3, 57947] ⟨1390729, 11, [(2, 3), (3, 1), (57947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_57947
  · decide +kernel

theorem prime_1390789 : Nat.Prime 1390789 := by
  apply nodeValid_prime [2, 3, 7, 5519] ⟨1390789, 2, [(2, 2), (3, 2), (7, 1), (5519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5519
  · decide +kernel

theorem prime_1512829 : Nat.Prime 1512829 := by
  apply nodeValid_prime [2, 3, 42023] ⟨1512829, 2, [(2, 2), (3, 2), (42023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42023
  · decide +kernel

theorem prime_1519619 : Nat.Prime 1519619 := by
  apply nodeValid_prime [2, 467, 1627] ⟨1519619, 2, [(2, 1), (467, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_467
    · exact prime_1627
  · decide +kernel

theorem prime_1683637 : Nat.Prime 1683637 := by
  apply nodeValid_prime [2, 3, 173, 811] ⟨1683637, 2, [(2, 2), (3, 1), (173, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_811
  · decide +kernel

theorem prime_2028511 : Nat.Prime 2028511 := by
  apply nodeValid_prime [2, 3, 5, 11, 683] ⟨2028511, 6, [(2, 1), (3, 3), (5, 1), (11, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_683
  · decide +kernel

theorem prime_2128409 : Nat.Prime 2128409 := by
  apply nodeValid_prime [2, 266051] ⟨2128409, 3, [(2, 3), (266051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_266051
  · decide +kernel

theorem prime_2281403 : Nat.Prime 2281403 := by
  apply nodeValid_prime [2, 409, 2789] ⟨2281403, 2, [(2, 1), (409, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_2789
  · decide +kernel

theorem prime_2400623 : Nat.Prime 2400623 := by
  apply nodeValid_prime [2, 7, 171473] ⟨2400623, 5, [(2, 1), (7, 1), (171473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_171473
  · decide +kernel

theorem prime_2596303 : Nat.Prime 2596303 := by
  apply nodeValid_prime [2, 3, 97, 1487] ⟨2596303, 3, [(2, 1), (3, 2), (97, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1487
  · decide +kernel

theorem prime_2877239 : Nat.Prime 2877239 := by
  apply nodeValid_prime [2, 7, 13, 15809] ⟨2877239, 7, [(2, 1), (7, 1), (13, 1), (15809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_15809
  · decide +kernel

theorem prime_2890619 : Nat.Prime 2890619 := by
  apply nodeValid_prime [2, 227, 6367] ⟨2890619, 2, [(2, 1), (227, 1), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_6367
  · decide +kernel

theorem prime_3012223 : Nat.Prime 3012223 := by
  apply nodeValid_prime [2, 3, 19, 26423] ⟨3012223, 3, [(2, 1), (3, 1), (19, 1), (26423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_26423
  · decide +kernel

theorem prime_3233333 : Nat.Prime 3233333 := by
  apply nodeValid_prime [2, 17, 2797] ⟨3233333, 2, [(2, 2), (17, 2), (2797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2797
  · decide +kernel

theorem prime_3384839 : Nat.Prime 3384839 := by
  apply nodeValid_prime [2, 107, 15817] ⟨3384839, 17, [(2, 1), (107, 1), (15817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_15817
  · decide +kernel

theorem prime_3534497 : Nat.Prime 3534497 := by
  apply nodeValid_prime [2, 7, 31, 509] ⟨3534497, 3, [(2, 5), (7, 1), (31, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_509
  · decide +kernel

theorem prime_4340881 : Nat.Prime 4340881 := by
  apply nodeValid_prime [2, 3, 5, 6029] ⟨4340881, 11, [(2, 4), (3, 2), (5, 1), (6029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6029
  · decide +kernel

theorem prime_5652799 : Nat.Prime 5652799 := by
  apply nodeValid_prime [2, 3, 83, 11351] ⟨5652799, 3, [(2, 1), (3, 1), (83, 1), (11351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_11351
  · decide +kernel

theorem prime_5781239 : Nat.Prime 5781239 := by
  apply nodeValid_prime [2, 2890619] ⟨5781239, 7, [(2, 1), (2890619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2890619
  · decide +kernel

theorem prime_5901257 : Nat.Prime 5901257 := by
  apply nodeValid_prime [2, 737657] ⟨5901257, 3, [(2, 3), (737657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_737657
  · decide +kernel

theorem prime_5990213 : Nat.Prime 5990213 := by
  apply nodeValid_prime [2, 23, 65111] ⟨5990213, 2, [(2, 2), (23, 1), (65111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_65111
  · decide +kernel

theorem prime_6426163 : Nat.Prime 6426163 := by
  apply nodeValid_prime [2, 3, 59, 2017] ⟨6426163, 2, [(2, 1), (3, 3), (59, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2017
  · decide +kernel

theorem prime_6792811 : Nat.Prime 6792811 := by
  apply nodeValid_prime [2, 3, 5, 226427] ⟨6792811, 2, [(2, 1), (3, 1), (5, 1), (226427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_226427
  · decide +kernel

theorem prime_13688419 : Nat.Prime 13688419 := by
  apply nodeValid_prime [2, 3, 2281403] ⟨13688419, 2, [(2, 1), (3, 1), (2281403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2281403
  · decide +kernel

theorem prime_20011723 : Nat.Prime 20011723 := by
  apply nodeValid_prime [2, 3, 181, 18427] ⟨20011723, 5, [(2, 1), (3, 1), (181, 1), (18427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_18427
  · decide +kernel

theorem prime_23939911 : Nat.Prime 23939911 := by
  apply nodeValid_prime [2, 3, 5, 17, 15647] ⟨23939911, 6, [(2, 1), (3, 2), (5, 1), (17, 1), (15647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_15647
  · decide +kernel

theorem prime_29146963 : Nat.Prime 29146963 := by
  apply nodeValid_prime [2, 3, 13, 433, 863] ⟨29146963, 5, [(2, 1), (3, 1), (13, 1), (433, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_433
    · exact prime_863
  · decide +kernel

theorem prime_33378937 : Nat.Prime 33378937 := by
  apply nodeValid_prime [2, 3, 1390789] ⟨33378937, 5, [(2, 3), (3, 1), (1390789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1390789
  · decide +kernel

theorem prime_38311363 : Nat.Prime 38311363 := by
  apply nodeValid_prime [2, 3, 2128409] ⟨38311363, 2, [(2, 1), (3, 2), (2128409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2128409
  · decide +kernel

theorem prime_49147003 : Nat.Prime 49147003 := by
  apply nodeValid_prime [2, 3, 277, 9857] ⟨49147003, 3, [(2, 1), (3, 2), (277, 1), (9857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_9857
  · decide +kernel

theorem prime_50305883 : Nat.Prime 50305883 := by
  apply nodeValid_prime [2, 11, 19, 120349] ⟨50305883, 2, [(2, 1), (11, 1), (19, 1), (120349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_120349
  · decide +kernel

theorem prime_65739073 : Nat.Prime 65739073 := by
  apply nodeValid_prime [2, 3, 7, 41, 1193] ⟨65739073, 17, [(2, 6), (3, 1), (7, 1), (41, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_1193
  · decide +kernel

theorem prime_78827641 : Nat.Prime 78827641 := by
  apply nodeValid_prime [2, 3, 5, 17, 2273] ⟨78827641, 23, [(2, 3), (3, 1), (5, 1), (17, 2), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_2273
  · decide +kernel

theorem prime_92406551 : Nat.Prime 92406551 := by
  apply nodeValid_prime [2, 5, 577, 3203] ⟨92406551, 23, [(2, 1), (5, 2), (577, 1), (3203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_577
    · exact prime_3203
  · decide +kernel

theorem prime_100611767 : Nat.Prime 100611767 := by
  apply nodeValid_prime [2, 50305883] ⟨100611767, 5, [(2, 1), (50305883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_50305883
  · decide +kernel

theorem prime_116624129 : Nat.Prime 116624129 := by
  apply nodeValid_prime [2, 19, 23977] ⟨116624129, 3, [(2, 8), (19, 1), (23977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23977
  · decide +kernel

theorem prime_284380331 : Nat.Prime 284380331 := by
  apply nodeValid_prime [2, 5, 13, 353, 6197] ⟨284380331, 2, [(2, 1), (5, 1), (13, 1), (353, 1), (6197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_353
    · exact prime_6197
  · decide +kernel

theorem prime_433858643 : Nat.Prime 433858643 := by
  apply nodeValid_prime [2, 7, 632447] ⟨433858643, 2, [(2, 1), (7, 3), (632447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_632447
  · decide +kernel

theorem prime_561082031 : Nat.Prime 561082031 := by
  apply nodeValid_prime [2, 5, 1307, 42929] ⟨561082031, 11, [(2, 1), (5, 1), (1307, 1), (42929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1307
    · exact prime_42929
  · decide +kernel

theorem prime_606530189 : Nat.Prime 606530189 := by
  apply nodeValid_prime [2, 11, 2213, 6229] ⟨606530189, 2, [(2, 2), (11, 1), (2213, 1), (6229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2213
    · exact prime_6229
  · decide +kernel

theorem prime_740017207 : Nat.Prime 740017207 := by
  apply nodeValid_prime [2, 3, 19, 73, 29641] ⟨740017207, 3, [(2, 1), (3, 2), (19, 1), (73, 1), (29641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_73
    · exact prime_29641
  · decide +kernel

theorem prime_989978557 : Nat.Prime 989978557 := by
  apply nodeValid_prime [2, 3, 7, 1683637] ⟨989978557, 2, [(2, 2), (3, 1), (7, 2), (1683637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1683637
  · decide +kernel

theorem prime_1898189687 : Nat.Prime 1898189687 := by
  apply nodeValid_prime [2, 71, 89, 150197] ⟨1898189687, 5, [(2, 1), (71, 1), (89, 1), (150197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_89
    · exact prime_150197
  · decide +kernel

theorem prime_2095155523 : Nat.Prime 2095155523 := by
  apply nodeValid_prime [2, 3, 31, 137, 27407] ⟨2095155523, 2, [(2, 1), (3, 2), (31, 1), (137, 1), (27407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_137
    · exact prime_27407
  · decide +kernel

theorem prime_3084558241 : Nat.Prime 3084558241 := by
  apply nodeValid_prime [2, 3, 5, 6426163] ⟨3084558241, 22, [(2, 5), (3, 1), (5, 1), (6426163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6426163
  · decide +kernel

theorem prime_3132789263 : Nat.Prime 3132789263 := by
  apply nodeValid_prime [2, 1249, 1254119] ⟨3132789263, 5, [(2, 1), (1249, 1), (1254119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1249
    · exact prime_1254119
  · decide +kernel

theorem prime_3208534907 : Nat.Prime 3208534907 := by
  apply nodeValid_prime [2, 31, 89, 18757] ⟨3208534907, 2, [(2, 1), (31, 2), (89, 1), (18757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_89
    · exact prime_18757
  · decide +kernel

theorem prime_4134933281 : Nat.Prime 4134933281 := by
  apply nodeValid_prime [2, 5, 359, 71987] ⟨4134933281, 3, [(2, 5), (5, 1), (359, 1), (71987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_359
    · exact prime_71987
  · decide +kernel

theorem prime_4140438877 : Nat.Prime 4140438877 := by
  apply nodeValid_prime [2, 3, 7, 17, 113, 2851] ⟨4140438877, 5, [(2, 2), (3, 3), (7, 1), (17, 1), (113, 1), (2851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_113
    · exact prime_2851
  · decide +kernel

theorem prime_4364107603 : Nat.Prime 4364107603 := by
  apply nodeValid_prime [2, 3, 523, 1390729] ⟨4364107603, 7, [(2, 1), (3, 1), (523, 1), (1390729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_1390729
  · decide +kernel

theorem prime_4934103637 : Nat.Prime 4934103637 := by
  apply nodeValid_prime [2, 3, 7, 11, 587, 827] ⟨4934103637, 5, [(2, 2), (3, 1), (7, 1), (11, 2), (587, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_587
    · exact prime_827
  · decide +kernel

theorem prime_5042954197 : Nat.Prime 5042954197 := by
  apply nodeValid_prime [2, 3, 7, 20011723] ⟨5042954197, 5, [(2, 2), (3, 2), (7, 1), (20011723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_20011723
  · decide +kernel

theorem prime_6202576433 : Nat.Prime 6202576433 := by
  apply nodeValid_prime [2, 13, 41, 53, 13723] ⟨6202576433, 3, [(2, 4), (13, 1), (41, 1), (53, 1), (13723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_53
    · exact prime_13723
  · decide +kernel

theorem prime_6869817739 : Nat.Prime 6869817739 := by
  apply nodeValid_prime [2, 3, 7, 2596303] ⟨6869817739, 2, [(2, 1), (3, 3), (7, 2), (2596303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2596303
  · decide +kernel

theorem prime_12579873139 : Nat.Prime 12579873139 := by
  apply nodeValid_prime [2, 3, 7, 23, 4340881] ⟨12579873139, 2, [(2, 1), (3, 2), (7, 1), (23, 1), (4340881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_4340881
  · decide +kernel

theorem prime_13860259603 : Nat.Prime 13860259603 := by
  apply nodeValid_prime [2, 3, 7, 239, 1380779] ⟨13860259603, 2, [(2, 1), (3, 1), (7, 1), (239, 1), (1380779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_239
    · exact prime_1380779
  · decide +kernel

theorem prime_20696889529 : Nat.Prime 20696889529 := by
  apply nodeValid_prime [2, 3, 7, 13688419] ⟨20696889529, 11, [(2, 3), (3, 3), (7, 1), (13688419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13688419
  · decide +kernel

theorem prime_20951555231 : Nat.Prime 20951555231 := by
  apply nodeValid_prime [2, 5, 2095155523] ⟨20951555231, 17, [(2, 1), (5, 1), (2095155523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2095155523
  · decide +kernel

theorem prime_21902606623 : Nat.Prime 21902606623 := by
  apply nodeValid_prime [2, 3, 13, 8147, 11489] ⟨21902606623, 3, [(2, 1), (3, 2), (13, 1), (8147, 1), (11489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_8147
    · exact prime_11489
  · decide +kernel

theorem prime_22092221023 : Nat.Prime 22092221023 := by
  apply nodeValid_prime [2, 3, 2423, 1519619] ⟨22092221023, 5, [(2, 1), (3, 1), (2423, 1), (1519619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2423
    · exact prime_1519619
  · decide +kernel

theorem prime_25160585039 : Nat.Prime 25160585039 := by
  apply nodeValid_prime [2, 17, 740017207] ⟨25160585039, 7, [(2, 1), (17, 1), (740017207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_740017207
  · decide +kernel

theorem prime_25241893921 : Nat.Prime 25241893921 := by
  apply nodeValid_prime [2, 3, 5, 271, 7187] ⟨25241893921, 7, [(2, 5), (3, 4), (5, 1), (271, 1), (7187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
    · exact prime_7187
  · decide +kernel

theorem prime_33008947637 : Nat.Prime 33008947637 := by
  apply nodeValid_prime [2, 7, 26927, 43781] ⟨33008947637, 2, [(2, 2), (7, 1), (26927, 1), (43781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_26927
    · exact prime_43781
  · decide +kernel

theorem prime_38959582267 : Nat.Prime 38959582267 := by
  apply nodeValid_prime [2, 3, 11, 97, 2028511] ⟨38959582267, 2, [(2, 1), (3, 2), (11, 1), (97, 1), (2028511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_2028511
  · decide +kernel

theorem prime_81901535329 : Nat.Prime 81901535329 := by
  apply nodeValid_prime [2, 3, 284380331] ⟨81901535329, 7, [(2, 5), (3, 2), (284380331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_284380331
  · decide +kernel

theorem prime_148861834393 : Nat.Prime 148861834393 := by
  apply nodeValid_prime [2, 3, 6202576433] ⟨148861834393, 5, [(2, 3), (3, 1), (6202576433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6202576433
  · decide +kernel

theorem prime_149506379863 : Nat.Prime 149506379863 := by
  apply nodeValid_prime [2, 3, 7, 211, 521, 32381] ⟨149506379863, 3, [(2, 1), (3, 1), (7, 1), (211, 1), (521, 1), (32381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_211
    · exact prime_521
    · exact prime_32381
  · decide +kernel

theorem prime_151288625911 : Nat.Prime 151288625911 := by
  apply nodeValid_prime [2, 3, 5, 5042954197] ⟨151288625911, 11, [(2, 1), (3, 1), (5, 1), (5042954197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5042954197
  · decide +kernel

theorem prime_223534193321 : Nat.Prime 223534193321 := by
  apply nodeValid_prime [2, 5, 71, 953, 82591] ⟨223534193321, 3, [(2, 3), (5, 1), (71, 1), (953, 1), (82591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_953
    · exact prime_82591
  · decide +kernel

theorem prime_226201712951 : Nat.Prime 226201712951 := by
  apply nodeValid_prime [2, 5, 31, 41, 127, 28027] ⟨226201712951, 7, [(2, 1), (5, 2), (31, 1), (41, 1), (127, 1), (28027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_41
    · exact prime_127
    · exact prime_28027
  · decide +kernel

theorem prime_296759311813 : Nat.Prime 296759311813 := by
  apply nodeValid_prime [2, 3, 19, 433858643] ⟨296759311813, 2, [(2, 2), (3, 2), (19, 1), (433858643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_433858643
  · decide +kernel

theorem prime_445138975507 : Nat.Prime 445138975507 := by
  apply nodeValid_prime [2, 3, 17, 4364107603] ⟨445138975507, 2, [(2, 1), (3, 1), (17, 1), (4364107603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4364107603
  · decide +kernel

theorem prime_449488065883 : Nat.Prime 449488065883 := by
  apply nodeValid_prime [2, 3, 1607, 5261, 8861] ⟨449488065883, 3, [(2, 1), (3, 1), (1607, 1), (5261, 1), (8861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1607
    · exact prime_5261
    · exact prime_8861
  · decide +kernel

theorem prime_896070391883 : Nat.Prime 896070391883 := by
  apply nodeValid_prime [2, 79259, 5652799] ⟨896070391883, 2, [(2, 1), (79259, 1), (5652799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79259
    · exact prime_5652799
  · decide +kernel

theorem prime_910663152629 : Nat.Prime 910663152629 := by
  apply nodeValid_prime [2, 19, 97, 419, 294821] ⟨910663152629, 2, [(2, 2), (19, 1), (97, 1), (419, 1), (294821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_97
    · exact prime_419
    · exact prime_294821
  · decide +kernel

theorem prime_1776705546817 : Nat.Prime 1776705546817 := by
  apply nodeValid_prime [2, 3, 3084558241] ⟨1776705546817, 5, [(2, 6), (3, 2), (3084558241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3084558241
  · decide +kernel

theorem prime_1776705547033 : Nat.Prime 1776705547033 := by
  apply nodeValid_prime [2, 3, 13, 1898189687] ⟨1776705547033, 5, [(2, 3), (3, 2), (13, 1), (1898189687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1898189687
  · decide +kernel

theorem prime_1776705557701 : Nat.Prime 1776705557701 := by
  apply nodeValid_prime [2, 3, 5, 43, 983, 140111] ⟨1776705557701, 2, [(2, 2), (3, 1), (5, 2), (43, 1), (983, 1), (140111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_983
    · exact prime_140111
  · decide +kernel

theorem prime_1778630029643 : Nat.Prime 1778630029643 := by
  apply nodeValid_prime [2, 587849, 1512829] ⟨1778630029643, 2, [(2, 1), (587849, 1), (1512829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_587849
    · exact prime_1512829
  · decide +kernel

theorem prime_1778630038271 : Nat.Prime 1778630038271 := by
  apply nodeValid_prime [2, 5, 317, 561082031] ⟨1778630038271, 7, [(2, 1), (5, 1), (317, 1), (561082031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_317
    · exact prime_561082031
  · decide +kernel

theorem prime_1778630038571 : Nat.Prime 1778630038571 := by
  apply nodeValid_prime [2, 5, 7, 11, 47, 49147003] ⟨1778630038571, 6, [(2, 1), (5, 1), (7, 1), (11, 1), (47, 1), (49147003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_47
    · exact prime_49147003
  · decide +kernel

theorem prime_1780555870417 : Nat.Prime 1780555870417 := by
  apply nodeValid_prime [2, 3, 19, 71, 79, 348077] ⟨1780555870417, 5, [(2, 4), (3, 1), (19, 1), (71, 1), (79, 1), (348077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_71
    · exact prime_79
    · exact prime_348077
  · decide +kernel

theorem prime_1780555870879 : Nat.Prime 1780555870879 := by
  apply nodeValid_prime [2, 3, 296759311813] ⟨1780555870879, 3, [(2, 1), (3, 1), (296759311813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_296759311813
  · decide +kernel

theorem prime_1780555902029 : Nat.Prime 1780555902029 := by
  apply nodeValid_prime [2, 445138975507] ⟨1780555902029, 2, [(2, 2), (445138975507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_445138975507
  · decide +kernel

theorem prime_1782483170959 : Nat.Prime 1782483170959 := by
  apply nodeValid_prime [2, 3, 7, 2447, 5781239] ⟨1782483170959, 7, [(2, 1), (3, 2), (7, 1), (2447, 1), (5781239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2447
    · exact prime_5781239
  · decide +kernel

theorem prime_1782483172399 : Nat.Prime 1782483172399 := by
  apply nodeValid_prime [2, 3, 33008947637] ⟨1782483172399, 3, [(2, 1), (3, 3), (33008947637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33008947637
  · decide +kernel

theorem prime_1782483187637 : Nat.Prime 1782483187637 := by
  apply nodeValid_prime [2, 3821, 116624129] ⟨1782483187637, 2, [(2, 2), (3821, 1), (116624129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3821
    · exact prime_116624129
  · decide +kernel

theorem prime_1784411816039 : Nat.Prime 1784411816039 := by
  apply nodeValid_prime [2, 1471, 606530189] ⟨1784411816039, 13, [(2, 1), (1471, 1), (606530189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1471
    · exact prime_606530189
  · decide +kernel

theorem prime_1784411816041 : Nat.Prime 1784411816041 := by
  apply nodeValid_prime [2, 3, 5, 7, 73, 3233333] ⟨1784411816041, 11, [(2, 3), (3, 3), (5, 1), (7, 1), (73, 1), (3233333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_73
    · exact prime_3233333
  · decide +kernel

theorem prime_1784411883377 : Nat.Prime 1784411883377 := by
  apply nodeValid_prime [2, 46457, 2400623] ⟨1784411883377, 3, [(2, 4), (46457, 1), (2400623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_46457
    · exact prime_2400623
  · decide +kernel

theorem prime_1786341985739 : Nat.Prime 1786341985739 := by
  apply nodeValid_prime [2, 71, 12579873139] ⟨1786341985739, 2, [(2, 1), (71, 1), (12579873139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_12579873139
  · decide +kernel

theorem prime_1786342012573 : Nat.Prime 1786342012573 := by
  apply nodeValid_prime [2, 3, 13, 17, 199, 3384839] ⟨1786342012573, 2, [(2, 2), (3, 1), (13, 1), (17, 1), (199, 1), (3384839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_199
    · exact prime_3384839
  · decide +kernel

theorem prime_1786342012717 : Nat.Prime 1786342012717 := by
  apply nodeValid_prime [2, 3, 148861834393] ⟨1786342012717, 6, [(2, 2), (3, 1), (148861834393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_148861834393
  · decide +kernel

theorem prime_1788273503921 : Nat.Prime 1788273503921 := by
  apply nodeValid_prime [2, 5, 1747, 3461, 3697] ⟨1788273503921, 3, [(2, 4), (5, 1), (1747, 1), (3461, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1747
    · exact prime_3461
    · exact prime_3697
  · decide +kernel

theorem prime_1788273546569 : Nat.Prime 1788273546569 := by
  apply nodeValid_prime [2, 223534193321] ⟨1788273546569, 3, [(2, 3), (223534193321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_223534193321
  · decide +kernel

theorem prime_1788273546659 : Nat.Prime 1788273546659 := by
  apply nodeValid_prime [2, 8887, 100611767] ⟨1788273546659, 2, [(2, 1), (8887, 1), (100611767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8887
    · exact prime_100611767
  · decide +kernel

theorem prime_1790206435937 : Nat.Prime 1790206435937 := by
  apply nodeValid_prime [2, 23, 37, 65739073] ⟨1790206435937, 3, [(2, 5), (23, 1), (37, 1), (65739073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_65739073
  · decide +kernel

theorem prime_1790206467461 : Nat.Prime 1790206467461 := by
  apply nodeValid_prime [2, 5, 37, 83, 29146963] ⟨1790206467461, 2, [(2, 2), (5, 1), (37, 1), (83, 1), (29146963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_83
    · exact prime_29146963
  · decide +kernel

theorem prime_1790206468103 : Nat.Prime 1790206468103 := by
  apply nodeValid_prime [2, 13, 19, 58907, 61519] ⟨1790206468103, 5, [(2, 1), (13, 1), (19, 1), (58907, 1), (61519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_58907
    · exact prime_61519
  · decide +kernel

theorem prime_1792140783767 : Nat.Prime 1792140783767 := by
  apply nodeValid_prime [2, 896070391883] ⟨1792140783767, 5, [(2, 1), (896070391883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_896070391883
  · decide +kernel

theorem prime_1792140784283 : Nat.Prime 1792140784283 := by
  apply nodeValid_prime [2, 23, 38959582267] ⟨1792140784283, 2, [(2, 1), (23, 1), (38959582267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_38959582267
  · decide +kernel

theorem prime_1792140789419 : Nat.Prime 1792140789419 := by
  apply nodeValid_prime [2, 7, 47, 4549, 598729] ⟨1792140789419, 2, [(2, 1), (7, 1), (47, 1), (4549, 1), (598729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_4549
    · exact prime_598729
  · decide +kernel

theorem prime_1794076544129 : Nat.Prime 1794076544129 := by
  apply nodeValid_prime [2, 11, 5011, 254281] ⟨1794076544129, 3, [(2, 7), (11, 1), (5011, 1), (254281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_5011
    · exact prime_254281
  · decide +kernel

theorem prime_1794076548113 : Nat.Prime 1794076548113 := by
  apply nodeValid_prime [2, 19001, 5901257] ⟨1794076548113, 3, [(2, 4), (19001, 1), (5901257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19001
    · exact prime_5901257
  · decide +kernel

theorem prime_1794076558357 : Nat.Prime 1794076558357 := by
  apply nodeValid_prime [2, 3, 149506379863] ⟨1794076558357, 5, [(2, 2), (3, 1), (149506379863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149506379863
  · decide +kernel

theorem prime_1796013723869 : Nat.Prime 1796013723869 := by
  apply nodeValid_prime [2, 7, 13, 4934103637] ⟨1796013723869, 2, [(2, 2), (7, 1), (13, 1), (4934103637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_4934103637
  · decide +kernel

theorem prime_1796013725237 : Nat.Prime 1796013725237 := by
  apply nodeValid_prime [2, 43, 113, 92406551] ⟨1796013725237, 2, [(2, 2), (43, 1), (113, 1), (92406551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_113
    · exact prime_92406551
  · decide +kernel

theorem prime_1796013743087 : Nat.Prime 1796013743087 := by
  apply nodeValid_prime [2, 41, 21902606623] ⟨1796013743087, 5, [(2, 1), (41, 1), (21902606623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_21902606623
  · decide +kernel

theorem prime_1797952263533 : Nat.Prime 1797952263533 := by
  apply nodeValid_prime [2, 449488065883] ⟨1797952263533, 2, [(2, 2), (449488065883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_449488065883
  · decide +kernel

theorem prime_1797952265591 : Nat.Prime 1797952265591 := by
  apply nodeValid_prime [2, 5, 13, 19, 38311363] ⟨1797952265591, 11, [(2, 1), (5, 1), (13, 1), (19, 2), (38311363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_38311363
  · decide +kernel

theorem prime_1797952339817 : Nat.Prime 1797952339817 := by
  apply nodeValid_prime [2, 43, 31277, 167107] ⟨1797952339817, 3, [(2, 3), (43, 1), (31277, 1), (167107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_31277
    · exact prime_167107
  · decide +kernel

theorem prime_1799892247591 : Nat.Prime 1799892247591 := by
  apply nodeValid_prime [2, 3, 5, 28729, 696119] ⟨1799892247591, 3, [(2, 1), (3, 2), (5, 1), (28729, 1), (696119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28729
    · exact prime_696119
  · decide +kernel

theorem prime_1799892247619 : Nat.Prime 1799892247619 := by
  apply nodeValid_prime [2, 131, 6869817739] ⟨1799892247619, 2, [(2, 1), (131, 1), (6869817739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_6869817739
  · decide +kernel

theorem prime_1799892349711 : Nat.Prime 1799892349711 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 233, 307, 709] ⟨1799892349711, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 2), (233, 1), (307, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_233
    · exact prime_307
    · exact prime_709
  · decide +kernel

theorem prime_1801833748391 : Nat.Prime 1801833748391 := by
  apply nodeValid_prime [2, 5, 13, 13860259603] ⟨1801833748391, 17, [(2, 1), (5, 1), (13, 1), (13860259603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_13860259603
  · decide +kernel

theorem prime_1801833749867 : Nat.Prime 1801833749867 := by
  apply nodeValid_prime [2, 43, 20951555231] ⟨1801833749867, 2, [(2, 1), (43, 1), (20951555231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_20951555231
  · decide +kernel

theorem prime_1801833777239 : Nat.Prime 1801833777239 := by
  apply nodeValid_prime [2, 11, 81901535329] ⟨1801833777239, 11, [(2, 1), (11, 1), (81901535329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_81901535329
  · decide +kernel

theorem prime_1803776534201 : Nat.Prime 1803776534201 := by
  apply nodeValid_prime [2, 5, 83, 191, 568907] ⟨1803776534201, 3, [(2, 3), (5, 2), (83, 1), (191, 1), (568907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_191
    · exact prime_568907
  · decide +kernel

theorem prime_1803776534207 : Nat.Prime 1803776534207 := by
  apply nodeValid_prime [2, 101, 373, 23939911] ⟨1803776534207, 5, [(2, 1), (101, 1), (373, 1), (23939911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_373
    · exact prime_23939911
  · decide +kernel

theorem prime_1803776618563 : Nat.Prime 1803776618563 := by
  apply nodeValid_prime [2, 3, 44257, 6792811] ⟨1803776618563, 5, [(2, 1), (3, 1), (44257, 1), (6792811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44257
    · exact prime_6792811
  · decide +kernel

theorem prime_1805720887969 : Nat.Prime 1805720887969 := by
  apply nodeValid_prime [2, 3, 19, 989978557] ⟨1805720887969, 7, [(2, 5), (3, 1), (19, 1), (989978557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_989978557
  · decide +kernel

theorem prime_1805720889991 : Nat.Prime 1805720889991 := by
  apply nodeValid_prime [2, 3, 5, 151, 487, 818509] ⟨1805720889991, 6, [(2, 1), (3, 1), (5, 1), (151, 1), (487, 1), (818509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_487
    · exact prime_818509
  · decide +kernel

theorem prime_1805720890013 : Nat.Prime 1805720890013 := by
  apply nodeValid_prime [2, 13, 71237, 487463] ⟨1805720890013, 2, [(2, 2), (13, 1), (71237, 1), (487463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71237
    · exact prime_487463
  · decide +kernel

theorem prime_1807666577011 : Nat.Prime 1807666577011 := by
  apply nodeValid_prime [2, 3, 5, 7, 479, 5990213] ⟨1807666577011, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (479, 1), (5990213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_479
    · exact prime_5990213
  · decide +kernel

theorem prime_1807666597189 : Nat.Prime 1807666597189 := by
  apply nodeValid_prime [2, 3, 809, 953, 65129] ⟨1807666597189, 6, [(2, 2), (3, 2), (809, 1), (953, 1), (65129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_809
    · exact prime_953
    · exact prime_65129
  · decide +kernel

theorem prime_1807666597211 : Nat.Prime 1807666597211 := by
  apply nodeValid_prime [2, 5, 47, 40507, 94949] ⟨1807666597211, 10, [(2, 1), (5, 1), (47, 1), (40507, 1), (94949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_40507
    · exact prime_94949
  · decide +kernel

theorem prime_1809613687549 : Nat.Prime 1809613687549 := by
  apply nodeValid_prime [2, 3, 47, 3208534907] ⟨1809613687549, 2, [(2, 2), (3, 1), (47, 1), (3208534907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_3208534907
  · decide +kernel

theorem prime_1809613703609 : Nat.Prime 1809613703609 := by
  apply nodeValid_prime [2, 226201712951] ⟨1809613703609, 3, [(2, 3), (226201712951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_226201712951
  · decide +kernel

theorem prime_1809613704929 : Nat.Prime 1809613704929 := by
  apply nodeValid_prime [2, 23, 26387, 93179] ⟨1809613704929, 3, [(2, 5), (23, 1), (26387, 1), (93179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_26387
    · exact prime_93179
  · decide +kernel

theorem prime_1811562122809 : Nat.Prime 1811562122809 := by
  apply nodeValid_prime [2, 3, 25160585039] ⟨1811562122809, 7, [(2, 3), (3, 2), (25160585039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25160585039
  · decide +kernel

theorem prime_1811562123887 : Nat.Prime 1811562123887 := by
  apply nodeValid_prime [2, 41, 22092221023] ⟨1811562123887, 5, [(2, 1), (41, 1), (22092221023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_22092221023
  · decide +kernel

theorem prime_1811562224789 : Nat.Prime 1811562224789 := by
  apply nodeValid_prime [2, 19, 911, 1377107] ⟨1811562224789, 2, [(2, 2), (19, 2), (911, 1), (1377107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_911
    · exact prime_1377107
  · decide +kernel

theorem prime_1813512186071 : Nat.Prime 1813512186071 := by
  apply nodeValid_prime [2, 5, 13, 103393, 134923] ⟨1813512186071, 11, [(2, 1), (5, 1), (13, 1), (103393, 1), (134923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_103393
    · exact prime_134923
  · decide +kernel

theorem prime_1813512227407 : Nat.Prime 1813512227407 := by
  apply nodeValid_prime [2, 3, 11, 61, 991, 454541] ⟨1813512227407, 3, [(2, 1), (3, 1), (11, 1), (61, 1), (991, 1), (454541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
    · exact prime_991
    · exact prime_454541
  · decide +kernel

theorem prime_1813512228127 : Nat.Prime 1813512228127 := by
  apply nodeValid_prime [2, 3, 73, 4140438877] ⟨1813512228127, 6, [(2, 1), (3, 1), (73, 1), (4140438877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_4140438877
  · decide +kernel

theorem prime_1815463508899 : Nat.Prime 1815463508899 := by
  apply nodeValid_prime [2, 3, 13, 29, 41, 109, 179591] ⟨1815463508899, 3, [(2, 1), (3, 1), (13, 1), (29, 1), (41, 1), (109, 1), (179591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_41
    · exact prime_109
    · exact prime_179591
  · decide +kernel

theorem prime_1815463510933 : Nat.Prime 1815463510933 := by
  apply nodeValid_prime [2, 3, 151288625911] ⟨1815463510933, 2, [(2, 2), (3, 1), (151288625911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151288625911
  · decide +kernel

theorem prime_1815463578811 : Nat.Prime 1815463578811 := by
  apply nodeValid_prime [2, 3, 5, 7, 113, 1249, 61253] ⟨1815463578811, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (1249, 1), (61253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_113
    · exact prime_1249
    · exact prime_61253
  · decide +kernel

theorem prime_1817416361777 : Nat.Prime 1817416361777 := by
  apply nodeValid_prime [2, 41, 83, 33378937] ⟨1817416361777, 3, [(2, 4), (41, 1), (83, 1), (33378937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_83
    · exact prime_33378937
  · decide +kernel

theorem prime_1817416362313 : Nat.Prime 1817416362313 := by
  apply nodeValid_prime [2, 3, 25241893921] ⟨1817416362313, 5, [(2, 3), (3, 2), (25241893921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25241893921
  · decide +kernel

theorem prime_1817416396511 : Nat.Prime 1817416396511 := by
  apply nodeValid_prime [2, 5, 11, 13, 1279, 993683] ⟨1817416396511, 7, [(2, 1), (5, 1), (11, 1), (13, 1), (1279, 1), (993683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_1279
    · exact prime_993683
  · decide +kernel

theorem prime_1819370630527 : Nat.Prime 1819370630527 := by
  apply nodeValid_prime [2, 3, 29, 397, 2819, 9343] ⟨1819370630527, 3, [(2, 1), (3, 1), (29, 1), (397, 1), (2819, 1), (9343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_397
    · exact prime_2819
    · exact prime_9343
  · decide +kernel

theorem prime_1819370643109 : Nat.Prime 1819370643109 := by
  apply nodeValid_prime [2, 3, 50333, 3012223] ⟨1819370643109, 2, [(2, 2), (3, 1), (50333, 1), (3012223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50333
    · exact prime_3012223
  · decide +kernel

theorem prime_1819370643641 : Nat.Prime 1819370643641 := by
  apply nodeValid_prime [2, 5, 11, 4134933281] ⟨1819370643641, 3, [(2, 3), (5, 1), (11, 1), (4134933281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_4134933281
  · decide +kernel

theorem prime_1821326278553 : Nat.Prime 1821326278553 := by
  apply nodeValid_prime [2, 11, 20696889529] ⟨1821326278553, 3, [(2, 3), (11, 1), (20696889529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_20696889529
  · decide +kernel

theorem prime_1821326304101 : Nat.Prime 1821326304101 := by
  apply nodeValid_prime [2, 5, 5153, 3534497] ⟨1821326304101, 2, [(2, 2), (5, 2), (5153, 1), (3534497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5153
    · exact prime_3534497
  · decide +kernel

theorem prime_1821326305259 : Nat.Prime 1821326305259 := by
  apply nodeValid_prime [2, 910663152629] ⟨1821326305259, 2, [(2, 1), (910663152629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_910663152629
  · decide +kernel

theorem prime_1823283336331 : Nat.Prime 1823283336331 := by
  apply nodeValid_prime [2, 3, 5, 257, 78827641] ⟨1823283336331, 2, [(2, 1), (3, 2), (5, 1), (257, 1), (78827641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
    · exact prime_78827641
  · decide +kernel

theorem prime_1823283336389 : Nat.Prime 1823283336389 := by
  apply nodeValid_prime [2, 17, 9319, 2877239] ⟨1823283336389, 2, [(2, 2), (17, 1), (9319, 1), (2877239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9319
    · exact prime_2877239
  · decide +kernel

theorem prime_1823283351067 : Nat.Prime 1823283351067 := by
  apply nodeValid_prime [2, 3, 97, 3132789263] ⟨1823283351067, 2, [(2, 1), (3, 1), (97, 1), (3132789263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_3132789263
  · decide +kernel

end Sude.Lucas.Generated
