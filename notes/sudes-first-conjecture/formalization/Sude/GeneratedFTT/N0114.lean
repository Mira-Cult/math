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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0100

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7817 : Nat.Prime 7817 := by
  apply nodeValid_prime [2, 977] ⟨7817, 3, [(2, 3), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_977
  · decide +kernel

theorem prime_15937 : Nat.Prime 15937 := by
  apply nodeValid_prime [2, 3, 83] ⟨15937, 7, [(2, 6), (3, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_19219 : Nat.Prime 19219 := by
  apply nodeValid_prime [2, 3, 3203] ⟨19219, 2, [(2, 1), (3, 1), (3203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3203
  · decide +kernel

theorem prime_21101 : Nat.Prime 21101 := by
  apply nodeValid_prime [2, 5, 211] ⟨21101, 2, [(2, 2), (5, 2), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
  · decide +kernel

theorem prime_24979 : Nat.Prime 24979 := by
  apply nodeValid_prime [2, 3, 23, 181] ⟨24979, 2, [(2, 1), (3, 1), (23, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_181
  · decide +kernel

theorem prime_30497 : Nat.Prime 30497 := by
  apply nodeValid_prime [2, 953] ⟨30497, 3, [(2, 5), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_953
  · decide +kernel

theorem prime_30781 : Nat.Prime 30781 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨30781, 2, [(2, 2), (3, 4), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_31387 : Nat.Prime 31387 := by
  apply nodeValid_prime [2, 3, 5231] ⟨31387, 2, [(2, 1), (3, 1), (5231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5231
  · decide +kernel

theorem prime_41959 : Nat.Prime 41959 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨41959, 6, [(2, 1), (3, 4), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_42841 : Nat.Prime 42841 := by
  apply nodeValid_prime [2, 3, 5, 7, 17] ⟨42841, 23, [(2, 3), (3, 2), (5, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_43189 : Nat.Prime 43189 := by
  apply nodeValid_prime [2, 3, 59, 61] ⟨43189, 2, [(2, 2), (3, 1), (59, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_61
  · decide +kernel

theorem prime_43627 : Nat.Prime 43627 := by
  apply nodeValid_prime [2, 3, 11, 661] ⟨43627, 2, [(2, 1), (3, 1), (11, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_661
  · decide +kernel

theorem prime_45263 : Nat.Prime 45263 := by
  apply nodeValid_prime [2, 7, 53, 61] ⟨45263, 5, [(2, 1), (7, 1), (53, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_61
  · decide +kernel

theorem prime_56453 : Nat.Prime 56453 := by
  apply nodeValid_prime [2, 11, 1283] ⟨56453, 2, [(2, 2), (11, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1283
  · decide +kernel

theorem prime_62617 : Nat.Prime 62617 := by
  apply nodeValid_prime [2, 3, 2609] ⟨62617, 5, [(2, 3), (3, 1), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2609
  · decide +kernel

theorem prime_67993 : Nat.Prime 67993 := by
  apply nodeValid_prime [2, 3, 2833] ⟨67993, 5, [(2, 3), (3, 1), (2833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2833
  · decide +kernel

theorem prime_70297 : Nat.Prime 70297 := by
  apply nodeValid_prime [2, 3, 29, 101] ⟨70297, 5, [(2, 3), (3, 1), (29, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_101
  · decide +kernel

theorem prime_70769 : Nat.Prime 70769 := by
  apply nodeValid_prime [2, 4423] ⟨70769, 3, [(2, 4), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4423
  · decide +kernel

theorem prime_74941 : Nat.Prime 74941 := by
  apply nodeValid_prime [2, 3, 5, 1249] ⟨74941, 6, [(2, 2), (3, 1), (5, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1249
  · decide +kernel

theorem prime_79427 : Nat.Prime 79427 := by
  apply nodeValid_prime [2, 151, 263] ⟨79427, 2, [(2, 1), (151, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_263
  · decide +kernel

theorem prime_82529 : Nat.Prime 82529 := by
  apply nodeValid_prime [2, 2579] ⟨82529, 3, [(2, 5), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2579
  · decide +kernel

theorem prime_83389 : Nat.Prime 83389 := by
  apply nodeValid_prime [2, 3, 6949] ⟨83389, 2, [(2, 2), (3, 1), (6949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6949
  · decide +kernel

theorem prime_89849 : Nat.Prime 89849 := by
  apply nodeValid_prime [2, 11, 1021] ⟨89849, 3, [(2, 3), (11, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1021
  · decide +kernel

theorem prime_93077 : Nat.Prime 93077 := by
  apply nodeValid_prime [2, 23269] ⟨93077, 2, [(2, 2), (23269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23269
  · decide +kernel

theorem prime_135607 : Nat.Prime 135607 := by
  apply nodeValid_prime [2, 3, 97, 233] ⟨135607, 3, [(2, 1), (3, 1), (97, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_233
  · decide +kernel

theorem prime_137369 : Nat.Prime 137369 := by
  apply nodeValid_prime [2, 7, 11, 223] ⟨137369, 6, [(2, 3), (7, 1), (11, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_223
  · decide +kernel

theorem prime_138577 : Nat.Prime 138577 := by
  apply nodeValid_prime [2, 3, 2887] ⟨138577, 5, [(2, 4), (3, 1), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2887
  · decide +kernel

theorem prime_162053 : Nat.Prime 162053 := by
  apply nodeValid_prime [2, 11, 29, 127] ⟨162053, 2, [(2, 2), (11, 1), (29, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_127
  · decide +kernel

theorem prime_164443 : Nat.Prime 164443 := by
  apply nodeValid_prime [2, 3, 27407] ⟨164443, 2, [(2, 1), (3, 1), (27407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27407
  · decide +kernel

theorem prime_181063 : Nat.Prime 181063 := by
  apply nodeValid_prime [2, 3, 7, 479] ⟨181063, 5, [(2, 1), (3, 3), (7, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_479
  · decide +kernel

theorem prime_184687 : Nat.Prime 184687 := by
  apply nodeValid_prime [2, 3, 30781] ⟨184687, 3, [(2, 1), (3, 1), (30781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30781
  · decide +kernel

theorem prime_192461 : Nat.Prime 192461 := by
  apply nodeValid_prime [2, 5, 9623] ⟨192461, 2, [(2, 2), (5, 1), (9623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9623
  · decide +kernel

theorem prime_201437 : Nat.Prime 201437 := by
  apply nodeValid_prime [2, 50359] ⟨201437, 2, [(2, 2), (50359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_50359
  · decide +kernel

theorem prime_209639 : Nat.Prime 209639 := by
  apply nodeValid_prime [2, 11, 13, 733] ⟨209639, 11, [(2, 1), (11, 1), (13, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_733
  · decide +kernel

theorem prime_221201 : Nat.Prime 221201 := by
  apply nodeValid_prime [2, 5, 7, 79] ⟨221201, 11, [(2, 4), (5, 2), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_245681 : Nat.Prime 245681 := by
  apply nodeValid_prime [2, 5, 37, 83] ⟨245681, 3, [(2, 4), (5, 1), (37, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_83
  · decide +kernel

theorem prime_260009 : Nat.Prime 260009 := by
  apply nodeValid_prime [2, 7, 4643] ⟨260009, 3, [(2, 3), (7, 1), (4643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4643
  · decide +kernel

theorem prime_260573 : Nat.Prime 260573 := by
  apply nodeValid_prime [2, 13, 5011] ⟨260573, 2, [(2, 2), (13, 1), (5011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5011
  · decide +kernel

theorem prime_295751 : Nat.Prime 295751 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨295751, 11, [(2, 1), (5, 3), (7, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_319589 : Nat.Prime 319589 := by
  apply nodeValid_prime [2, 109, 733] ⟨319589, 2, [(2, 2), (109, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_733
  · decide +kernel

theorem prime_328621 : Nat.Prime 328621 := by
  apply nodeValid_prime [2, 3, 5, 5477] ⟨328621, 6, [(2, 2), (3, 1), (5, 1), (5477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5477
  · decide +kernel

theorem prime_366077 : Nat.Prime 366077 := by
  apply nodeValid_prime [2, 71, 1289] ⟨366077, 2, [(2, 2), (71, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1289
  · decide +kernel

theorem prime_421783 : Nat.Prime 421783 := by
  apply nodeValid_prime [2, 3, 70297] ⟨421783, 5, [(2, 1), (3, 1), (70297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_70297
  · decide +kernel

theorem prime_481489 : Nat.Prime 481489 := by
  apply nodeValid_prime [2, 3, 7, 1433] ⟨481489, 11, [(2, 4), (3, 1), (7, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1433
  · decide +kernel

theorem prime_484987 : Nat.Prime 484987 := by
  apply nodeValid_prime [2, 3, 80831] ⟨484987, 2, [(2, 1), (3, 1), (80831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80831
  · decide +kernel

theorem prime_504617 : Nat.Prime 504617 := by
  apply nodeValid_prime [2, 7, 9011] ⟨504617, 3, [(2, 3), (7, 1), (9011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9011
  · decide +kernel

theorem prime_505759 : Nat.Prime 505759 := by
  apply nodeValid_prime [2, 3, 11, 79, 97] ⟨505759, 3, [(2, 1), (3, 1), (11, 1), (79, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
    · exact prime_97
  · decide +kernel

theorem prime_510589 : Nat.Prime 510589 := by
  apply nodeValid_prime [2, 3, 13, 1091] ⟨510589, 6, [(2, 2), (3, 2), (13, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1091
  · decide +kernel

theorem prime_553153 : Nat.Prime 553153 := by
  apply nodeValid_prime [2, 3, 43, 67] ⟨553153, 5, [(2, 6), (3, 1), (43, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_67
  · decide +kernel

theorem prime_730399 : Nat.Prime 730399 := by
  apply nodeValid_prime [2, 3, 19, 43, 149] ⟨730399, 6, [(2, 1), (3, 1), (19, 1), (43, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_43
    · exact prime_149
  · decide +kernel

theorem prime_942541 : Nat.Prime 942541 := by
  apply nodeValid_prime [2, 3, 5, 23, 683] ⟨942541, 6, [(2, 2), (3, 1), (5, 1), (23, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_683
  · decide +kernel

theorem prime_986659 : Nat.Prime 986659 := by
  apply nodeValid_prime [2, 3, 164443] ⟨986659, 2, [(2, 1), (3, 1), (164443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_164443
  · decide +kernel

theorem prime_1677113 : Nat.Prime 1677113 := by
  apply nodeValid_prime [2, 209639] ⟨1677113, 3, [(2, 3), (209639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_209639
  · decide +kernel

theorem prime_1716733 : Nat.Prime 1716733 := by
  apply nodeValid_prime [2, 3, 43, 1109] ⟨1716733, 2, [(2, 2), (3, 2), (43, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1109
  · decide +kernel

theorem prime_1798801 : Nat.Prime 1798801 := by
  apply nodeValid_prime [2, 3, 5, 1499] ⟨1798801, 17, [(2, 4), (3, 1), (5, 2), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1499
  · decide +kernel

theorem prime_2064317 : Nat.Prime 2064317 := by
  apply nodeValid_prime [2, 137, 3767] ⟨2064317, 2, [(2, 2), (137, 1), (3767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_3767
  · decide +kernel

theorem prime_2156377 : Nat.Prime 2156377 := by
  apply nodeValid_prime [2, 3, 89849] ⟨2156377, 5, [(2, 3), (3, 1), (89849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89849
  · decide +kernel

theorem prime_2446013 : Nat.Prime 2446013 := by
  apply nodeValid_prime [2, 43, 14221] ⟨2446013, 2, [(2, 2), (43, 1), (14221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_14221
  · decide +kernel

theorem prime_3522569 : Nat.Prime 3522569 := by
  apply nodeValid_prime [2, 7, 62903] ⟨3522569, 3, [(2, 3), (7, 1), (62903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_62903
  · decide +kernel

theorem prime_4007039 : Nat.Prime 4007039 := by
  apply nodeValid_prime [2, 7, 79, 3623] ⟨4007039, 11, [(2, 1), (7, 1), (79, 1), (3623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_3623
  · decide +kernel

theorem prime_4472297 : Nat.Prime 4472297 := by
  apply nodeValid_prime [2, 19, 29423] ⟨4472297, 3, [(2, 3), (19, 1), (29423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29423
  · decide +kernel

theorem prime_4975079 : Nat.Prime 4975079 := by
  apply nodeValid_prime [2, 601, 4139] ⟨4975079, 7, [(2, 1), (601, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_4139
  · decide +kernel

theorem prime_5661521 : Nat.Prime 5661521 := by
  apply nodeValid_prime [2, 5, 70769] ⟨5661521, 3, [(2, 4), (5, 1), (70769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_70769
  · decide +kernel

theorem prime_5833909 : Nat.Prime 5833909 := by
  apply nodeValid_prime [2, 3, 162053] ⟨5833909, 2, [(2, 2), (3, 2), (162053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_162053
  · decide +kernel

theorem prime_5908519 : Nat.Prime 5908519 := by
  apply nodeValid_prime [2, 3, 7, 11, 29] ⟨5908519, 6, [(2, 1), (3, 3), (7, 3), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_7045139 : Nat.Prime 7045139 := by
  apply nodeValid_prime [2, 3522569] ⟨7045139, 2, [(2, 1), (3522569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3522569
  · decide +kernel

theorem prime_7334869 : Nat.Prime 7334869 := by
  apply nodeValid_prime [2, 3, 71, 8609] ⟨7334869, 2, [(2, 2), (3, 1), (71, 1), (8609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_8609
  · decide +kernel

theorem prime_7621813 : Nat.Prime 7621813 := by
  apply nodeValid_prime [2, 3, 11, 19, 1013] ⟨7621813, 2, [(2, 2), (3, 2), (11, 1), (19, 1), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_1013
  · decide +kernel

theorem prime_7916399 : Nat.Prime 7916399 := by
  apply nodeValid_prime [2, 7, 47, 53, 227] ⟨7916399, 7, [(2, 1), (7, 1), (47, 1), (53, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_53
    · exact prime_227
  · decide +kernel

theorem prime_8242141 : Nat.Prime 8242141 := by
  apply nodeValid_prime [2, 3, 5, 137369] ⟨8242141, 2, [(2, 2), (3, 1), (5, 1), (137369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137369
  · decide +kernel

theorem prime_8897311 : Nat.Prime 8897311 := by
  apply nodeValid_prime [2, 3, 5, 31, 1063] ⟨8897311, 3, [(2, 1), (3, 3), (5, 1), (31, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1063
  · decide +kernel

theorem prime_17088293 : Nat.Prime 17088293 := by
  apply nodeValid_prime [2, 13, 328621] ⟨17088293, 2, [(2, 2), (13, 1), (328621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_328621
  · decide +kernel

theorem prime_19290221 : Nat.Prime 19290221 := by
  apply nodeValid_prime [2, 5, 29, 79, 421] ⟨19290221, 2, [(2, 2), (5, 1), (29, 1), (79, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_79
    · exact prime_421
  · decide +kernel

theorem prime_19666259 : Nat.Prime 19666259 := by
  apply nodeValid_prime [2, 617, 15937] ⟨19666259, 2, [(2, 1), (617, 1), (15937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_617
    · exact prime_15937
  · decide +kernel

theorem prime_25230851 : Nat.Prime 25230851 := by
  apply nodeValid_prime [2, 5, 504617] ⟨25230851, 6, [(2, 1), (5, 2), (504617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_504617
  · decide +kernel

theorem prime_27376259 : Nat.Prime 27376259 := by
  apply nodeValid_prime [2, 7, 13, 349, 431] ⟨27376259, 2, [(2, 1), (7, 1), (13, 1), (349, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_349
    · exact prime_431
  · decide +kernel

theorem prime_30345541 : Nat.Prime 30345541 := by
  apply nodeValid_prime [2, 3, 5, 505759] ⟨30345541, 2, [(2, 2), (3, 1), (5, 1), (505759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_505759
  · decide +kernel

theorem prime_30487253 : Nat.Prime 30487253 := by
  apply nodeValid_prime [2, 7621813] ⟨30487253, 2, [(2, 2), (7621813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7621813
  · decide +kernel

theorem prime_31050709 : Nat.Prime 31050709 := by
  apply nodeValid_prime [2, 3, 13, 61, 251] ⟨31050709, 6, [(2, 2), (3, 1), (13, 2), (61, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
    · exact prime_251
  · decide +kernel

theorem prime_37768127 : Nat.Prime 37768127 := by
  apply nodeValid_prime [2, 11, 1716733] ⟨37768127, 5, [(2, 1), (11, 1), (1716733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1716733
  · decide +kernel

theorem prime_44283581 : Nat.Prime 44283581 := by
  apply nodeValid_prime [2, 5, 11, 29, 631] ⟨44283581, 7, [(2, 2), (5, 1), (11, 2), (29, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_631
  · decide +kernel

theorem prime_53161327 : Nat.Prime 53161327 := by
  apply nodeValid_prime [2, 3, 23, 1861] ⟨53161327, 3, [(2, 1), (3, 3), (23, 2), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1861
  · decide +kernel

theorem prime_62115181 : Nat.Prime 62115181 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 103] ⟨62115181, 17, [(2, 2), (3, 1), (5, 1), (19, 1), (23, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_103
  · decide +kernel

theorem prime_66536611 : Nat.Prime 66536611 := by
  apply nodeValid_prime [2, 3, 5, 7, 45263] ⟨66536611, 7, [(2, 1), (3, 1), (5, 1), (7, 2), (45263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_45263
  · decide +kernel

theorem prime_98150803 : Nat.Prime 98150803 := by
  apply nodeValid_prime [2, 3, 41, 89, 4483] ⟨98150803, 2, [(2, 1), (3, 1), (41, 1), (89, 1), (4483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_89
    · exact prime_4483
  · decide +kernel

theorem prime_108932927 : Nat.Prime 108932927 := by
  apply nodeValid_prime [2, 283, 192461] ⟨108932927, 5, [(2, 1), (283, 1), (192461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_192461
  · decide +kernel

theorem prime_154717951 : Nat.Prime 154717951 := by
  apply nodeValid_prime [2, 3, 5, 19, 54287] ⟨154717951, 3, [(2, 1), (3, 1), (5, 2), (19, 1), (54287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_54287
  · decide +kernel

theorem prime_163848539 : Nat.Prime 163848539 := by
  apply nodeValid_prime [2, 7, 691, 16937] ⟨163848539, 2, [(2, 1), (7, 1), (691, 1), (16937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_691
    · exact prime_16937
  · decide +kernel

theorem prime_163917521 : Nat.Prime 163917521 := by
  apply nodeValid_prime [2, 5, 13, 277, 569] ⟨163917521, 3, [(2, 4), (5, 1), (13, 1), (277, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_277
    · exact prime_569
  · decide +kernel

theorem prime_201846809 : Nat.Prime 201846809 := by
  apply nodeValid_prime [2, 25230851] ⟨201846809, 3, [(2, 3), (25230851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25230851
  · decide +kernel

theorem prime_226650317 : Nat.Prime 226650317 := by
  apply nodeValid_prime [2, 19, 1151, 2591] ⟨226650317, 2, [(2, 2), (19, 1), (1151, 1), (2591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1151
    · exact prime_2591
  · decide +kernel

theorem prime_241160989 : Nat.Prime 241160989 := by
  apply nodeValid_prime [2, 3, 241, 83389] ⟨241160989, 2, [(2, 2), (3, 1), (241, 1), (83389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_83389
  · decide +kernel

theorem prime_265701487 : Nat.Prime 265701487 := by
  apply nodeValid_prime [2, 3, 44283581] ⟨265701487, 6, [(2, 1), (3, 1), (44283581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44283581
  · decide +kernel

theorem prime_277707011 : Nat.Prime 277707011 := by
  apply nodeValid_prime [2, 5, 7, 439, 1291] ⟨277707011, 2, [(2, 1), (5, 1), (7, 2), (439, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_439
    · exact prime_1291
  · decide +kernel

theorem prime_293721047 : Nat.Prime 293721047 := by
  apply nodeValid_prime [2, 43, 79427] ⟨293721047, 5, [(2, 1), (43, 2), (79427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_79427
  · decide +kernel

theorem prime_327697079 : Nat.Prime 327697079 := by
  apply nodeValid_prime [2, 163848539] ⟨327697079, 13, [(2, 1), (163848539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163848539
  · decide +kernel

theorem prime_372691087 : Nat.Prime 372691087 := by
  apply nodeValid_prime [2, 3, 62115181] ⟨372691087, 3, [(2, 1), (3, 1), (62115181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62115181
  · decide +kernel

theorem prime_483462911 : Nat.Prime 483462911 := by
  apply nodeValid_prime [2, 5, 7, 986659] ⟨483462911, 7, [(2, 1), (5, 1), (7, 2), (986659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_986659
  · decide +kernel

theorem prime_522586901 : Nat.Prime 522586901 := by
  apply nodeValid_prime [2, 5, 11, 43189] ⟨522586901, 2, [(2, 2), (5, 2), (11, 2), (43189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43189
  · decide +kernel

theorem prime_787328239 : Nat.Prime 787328239 := by
  apply nodeValid_prime [2, 3, 257, 510589] ⟨787328239, 6, [(2, 1), (3, 1), (257, 1), (510589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_510589
  · decide +kernel

theorem prime_865315397 : Nat.Prime 865315397 := by
  apply nodeValid_prime [2, 11, 19666259] ⟨865315397, 2, [(2, 2), (11, 1), (19666259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19666259
  · decide +kernel

theorem prime_1080252377 : Nat.Prime 1080252377 := by
  apply nodeValid_prime [2, 7, 19290221] ⟨1080252377, 3, [(2, 3), (7, 1), (19290221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19290221
  · decide +kernel

theorem prime_1180017947 : Nat.Prime 1180017947 := by
  apply nodeValid_prime [2, 29, 101, 201437] ⟨1180017947, 2, [(2, 1), (29, 1), (101, 1), (201437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_101
    · exact prime_201437
  · decide +kernel

theorem prime_3173104439 : Nat.Prime 3173104439 := by
  apply nodeValid_prime [2, 7, 226650317] ⟨3173104439, 7, [(2, 1), (7, 1), (226650317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_226650317
  · decide +kernel

theorem prime_4112094659 : Nat.Prime 4112094659 := by
  apply nodeValid_prime [2, 7, 293721047] ⟨4112094659, 2, [(2, 1), (7, 1), (293721047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_293721047
  · decide +kernel

theorem prime_6543818497 : Nat.Prime 6543818497 := by
  apply nodeValid_prime [2, 3, 946733] ⟨6543818497, 7, [(2, 8), (3, 3), (946733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_946733
  · decide +kernel

theorem prime_6740132011 : Nat.Prime 6740132011 := by
  apply nodeValid_prime [2, 3, 5, 19, 37, 319589] ⟨6740132011, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (37, 1), (319589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_37
    · exact prime_319589
  · decide +kernel

theorem prime_10163054893 : Nat.Prime 10163054893 := by
  apply nodeValid_prime [2, 3, 89, 106921] ⟨10163054893, 2, [(2, 2), (3, 1), (89, 2), (106921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_106921
  · decide +kernel

theorem prime_15802426907 : Nat.Prime 15802426907 := by
  apply nodeValid_prime [2, 7, 67, 181, 93077] ⟨15802426907, 2, [(2, 1), (7, 1), (67, 1), (181, 1), (93077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_181
    · exact prime_93077
  · decide +kernel

theorem prime_16315865063 : Nat.Prime 16315865063 := by
  apply nodeValid_prime [2, 7, 37, 601, 7487] ⟨16315865063, 10, [(2, 1), (7, 2), (37, 1), (601, 1), (7487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_601
    · exact prime_7487
  · decide +kernel

theorem prime_20865481327 : Nat.Prime 20865481327 := by
  apply nodeValid_prime [2, 3, 233, 4975079] ⟨20865481327, 3, [(2, 1), (3, 2), (233, 1), (4975079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_4975079
  · decide +kernel

theorem prime_25064308063 : Nat.Prime 25064308063 := by
  apply nodeValid_prime [2, 3, 154717951] ⟨25064308063, 5, [(2, 1), (3, 4), (154717951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_154717951
  · decide +kernel

theorem prime_30113884901 : Nat.Prime 30113884901 := by
  apply nodeValid_prime [2, 5, 11, 27376259] ⟨30113884901, 2, [(2, 2), (5, 2), (11, 1), (27376259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_27376259
  · decide +kernel

theorem prime_47750812289 : Nat.Prime 47750812289 := by
  apply nodeValid_prime [2, 173, 2156377] ⟨47750812289, 3, [(2, 7), (173, 1), (2156377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_2156377
  · decide +kernel

theorem prime_49078638877 : Nat.Prime 49078638877 := by
  apply nodeValid_prime [2, 3, 107, 4723, 8093] ⟨49078638877, 2, [(2, 2), (3, 1), (107, 1), (4723, 1), (8093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_4723
    · exact prime_8093
  · decide +kernel

theorem prime_52213994389 : Nat.Prime 52213994389 := by
  apply nodeValid_prime [2, 3, 483462911] ⟨52213994389, 6, [(2, 2), (3, 3), (483462911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_483462911
  · decide +kernel

theorem prime_81156089153 : Nat.Prime 81156089153 := by
  apply nodeValid_prime [2, 4877, 260009] ⟨81156089153, 3, [(2, 6), (4877, 1), (260009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4877
    · exact prime_260009
  · decide +kernel

theorem prime_121144155581 : Nat.Prime 121144155581 := by
  apply nodeValid_prime [2, 5, 7, 865315397] ⟨121144155581, 2, [(2, 2), (5, 1), (7, 1), (865315397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_865315397
  · decide +kernel

theorem prime_215946011081 : Nat.Prime 215946011081 := by
  apply nodeValid_prime [2, 5, 41, 971, 135607] ⟨215946011081, 3, [(2, 3), (5, 1), (41, 1), (971, 1), (135607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_971
    · exact prime_135607
  · decide +kernel

theorem prime_360202673339 : Nat.Prime 360202673339 := by
  apply nodeValid_prime [2, 61, 109, 863, 31387] ⟨360202673339, 2, [(2, 1), (61, 1), (109, 1), (863, 1), (31387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_109
    · exact prime_863
    · exact prime_31387
  · decide +kernel

theorem prime_435765650107 : Nat.Prime 435765650107 := by
  apply nodeValid_prime [2, 3, 2339, 31050709] ⟨435765650107, 2, [(2, 1), (3, 1), (2339, 1), (31050709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2339
    · exact prime_31050709
  · decide +kernel

theorem prime_726276083521 : Nat.Prime 726276083521 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 29, 118043] ⟨726276083521, 11, [(2, 6), (3, 1), (5, 1), (13, 1), (17, 1), (29, 1), (118043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_29
    · exact prime_118043
  · decide +kernel

theorem prime_728043597563 : Nat.Prime 728043597563 := by
  apply nodeValid_prime [2, 5471, 66536611] ⟨728043597563, 2, [(2, 1), (5471, 1), (66536611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5471
    · exact prime_66536611
  · decide +kernel

theorem prime_2184130784411 : Nat.Prime 2184130784411 := by
  apply nodeValid_prime [2, 5, 5783, 37768127] ⟨2184130784411, 2, [(2, 1), (5, 1), (5783, 1), (37768127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5783
    · exact prime_37768127
  · decide +kernel

theorem prime_4318920208021 : Nat.Prime 4318920208021 := by
  apply nodeValid_prime [2, 3, 5, 11, 6543818497] ⟨4318920208021, 7, [(2, 2), (3, 1), (5, 1), (11, 1), (6543818497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_6543818497
  · decide +kernel

theorem prime_4318920221177 : Nat.Prime 4318920221177 := by
  apply nodeValid_prime [2, 11, 49078638877] ⟨4318920221177, 3, [(2, 3), (11, 1), (49078638877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_49078638877
  · decide +kernel

theorem prime_4318920221621 : Nat.Prime 4318920221621 := by
  apply nodeValid_prime [2, 5, 215946011081] ⟨4318920221621, 2, [(2, 2), (5, 1), (215946011081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_215946011081
  · decide +kernel

theorem prime_4322432032111 : Nat.Prime 4322432032111 := by
  apply nodeValid_prime [2, 3, 5, 61, 787328239] ⟨4322432032111, 3, [(2, 1), (3, 2), (5, 1), (61, 1), (787328239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_787328239
  · decide +kernel

theorem prime_4322432079961 : Nat.Prime 4322432079961 := by
  apply nodeValid_prime [2, 3, 5, 17449, 2064317] ⟨4322432079961, 19, [(2, 3), (3, 1), (5, 1), (17449, 1), (2064317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17449
    · exact prime_2064317
  · decide +kernel

theorem prime_4322432080069 : Nat.Prime 4322432080069 := by
  apply nodeValid_prime [2, 3, 360202673339] ⟨4322432080069, 2, [(2, 2), (3, 1), (360202673339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_360202673339
  · decide +kernel

theorem prime_4325945793703 : Nat.Prime 4325945793703 := by
  apply nodeValid_prime [2, 3, 13, 47, 1180017947] ⟨4325945793703, 7, [(2, 1), (3, 1), (13, 1), (47, 1), (1180017947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
    · exact prime_1180017947
  · decide +kernel

theorem prime_4325945819927 : Nat.Prime 4325945819927 := by
  apply nodeValid_prime [2, 366077, 5908519] ⟨4325945819927, 5, [(2, 1), (366077, 1), (5908519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_366077
    · exact prime_5908519
  · decide +kernel

theorem prime_4325945820683 : Nat.Prime 4325945820683 := by
  apply nodeValid_prime [2, 8969, 241160989] ⟨4325945820683, 2, [(2, 1), (8969, 1), (241160989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8969
    · exact prime_241160989
  · decide +kernel

theorem prime_4329461384419 : Nat.Prime 4329461384419 := by
  apply nodeValid_prime [2, 3, 71, 10163054893] ⟨4329461384419, 2, [(2, 1), (3, 1), (71, 1), (10163054893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_10163054893
  · decide +kernel

theorem prime_4329461386097 : Nat.Prime 4329461386097 := by
  apply nodeValid_prime [2, 7, 11, 877, 4007039] ⟨4329461386097, 3, [(2, 4), (7, 1), (11, 1), (877, 1), (4007039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_877
    · exact prime_4007039
  · decide +kernel

theorem prime_4329461475601 : Nat.Prime 4329461475601 := by
  apply nodeValid_prime [2, 3, 5, 31, 1553, 74941] ⟨4329461475601, 7, [(2, 4), (3, 1), (5, 2), (31, 1), (1553, 1), (74941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1553
    · exact prime_74941
  · decide +kernel

theorem prime_4332979084123 : Nat.Prime 4332979084123 := by
  apply nodeValid_prime [2, 3, 13, 61, 181, 1677113] ⟨4332979084123, 5, [(2, 1), (3, 2), (13, 1), (61, 1), (181, 1), (1677113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
    · exact prime_181
    · exact prime_1677113
  · decide +kernel

theorem prime_4332979106251 : Nat.Prime 4332979106251 := by
  apply nodeValid_prime [2, 3, 5, 5297, 43627] ⟨4332979106251, 2, [(2, 1), (3, 1), (5, 5), (5297, 1), (43627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5297
    · exact prime_43627
  · decide +kernel

theorem prime_4332979108309 : Nat.Prime 4332979108309 := by
  apply nodeValid_prime [2, 3, 73, 163, 30345541] ⟨4332979108309, 2, [(2, 2), (3, 1), (73, 1), (163, 1), (30345541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_163
    · exact prime_30345541
  · decide +kernel

theorem prime_4336498625161 : Nat.Prime 4336498625161 := by
  apply nodeValid_prime [2, 3, 5, 13, 491, 5661521] ⟨4336498625161, 7, [(2, 3), (3, 1), (5, 1), (13, 1), (491, 1), (5661521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_491
    · exact prime_5661521
  · decide +kernel

theorem prime_4336498778147 : Nat.Prime 4336498778147 := by
  apply nodeValid_prime [2, 22091, 98150803] ⟨4336498778147, 2, [(2, 1), (22091, 1), (98150803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_22091
    · exact prime_98150803
  · decide +kernel

theorem prime_4336498778621 : Nat.Prime 4336498778621 := by
  apply nodeValid_prime [2, 5, 47, 24979, 184687] ⟨4336498778621, 3, [(2, 2), (5, 1), (47, 1), (24979, 1), (184687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_24979
    · exact prime_184687
  · decide +kernel

theorem prime_4340020106759 : Nat.Prime 4340020106759 := by
  apply nodeValid_prime [2, 7, 19, 16315865063] ⟨4340020106759, 7, [(2, 1), (7, 1), (19, 1), (16315865063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_16315865063
  · decide +kernel

theorem prime_4340020114277 : Nat.Prime 4340020114277 := by
  apply nodeValid_prime [2, 7, 11, 43, 327697079] ⟨4340020114277, 3, [(2, 2), (7, 1), (11, 1), (43, 1), (327697079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_43
    · exact prime_327697079
  · decide +kernel

theorem prime_4340020116017 : Nat.Prime 4340020116017 := by
  apply nodeValid_prime [2, 13, 20865481327] ⟨4340020116017, 3, [(2, 4), (13, 1), (20865481327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_20865481327
  · decide +kernel

theorem prime_4343543512489 : Nat.Prime 4343543512489 := by
  apply nodeValid_prime [2, 3, 67993, 295751] ⟨4343543512489, 7, [(2, 3), (3, 3), (67993, 1), (295751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67993
    · exact prime_295751
  · decide +kernel

theorem prime_4343543518939 : Nat.Prime 4343543518939 := by
  apply nodeValid_prime [2, 3, 13, 29, 61, 4027, 7817] ⟨4343543518939, 3, [(2, 1), (3, 1), (13, 1), (29, 1), (61, 1), (4027, 1), (7817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_61
    · exact prime_4027
    · exact prime_7817
  · decide +kernel

theorem prime_4343543519209 : Nat.Prime 4343543519209 := by
  apply nodeValid_prime [2, 3, 109, 1567, 9721] ⟨4343543519209, 7, [(2, 3), (3, 1), (109, 2), (1567, 1), (9721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_1567
    · exact prime_9721
  · decide +kernel

theorem prime_4347068838769 : Nat.Prime 4347068838769 := by
  apply nodeValid_prime [2, 3, 372691087] ⟨4347068838769, 7, [(2, 4), (3, 6), (372691087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_372691087
  · decide +kernel

theorem prime_4347068839049 : Nat.Prime 4347068839049 := by
  apply nodeValid_prime [2, 13, 19, 1223, 1798801] ⟨4347068839049, 3, [(2, 3), (13, 1), (19, 1), (1223, 1), (1798801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_1223
    · exact prime_1798801
  · decide +kernel

theorem prime_4347068851679 : Nat.Prime 4347068851679 := by
  apply nodeValid_prime [2, 7, 61, 643, 7916399] ⟨4347068851679, 7, [(2, 1), (7, 1), (61, 1), (643, 1), (7916399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_643
    · exact prime_7916399
  · decide +kernel

theorem prime_4350596120419 : Nat.Prime 4350596120419 := by
  apply nodeValid_prime [2, 3, 41, 67, 1013, 260573] ⟨4350596120419, 2, [(2, 1), (3, 1), (41, 1), (67, 1), (1013, 1), (260573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_67
    · exact prime_1013
    · exact prime_260573
  · decide +kernel

theorem prime_4350596148139 : Nat.Prime 4350596148139 := by
  apply nodeValid_prime [2, 3, 2729, 265701487] ⟨4350596148139, 2, [(2, 1), (3, 1), (2729, 1), (265701487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2729
    · exact prime_265701487
  · decide +kernel

theorem prime_4350596149223 : Nat.Prime 4350596149223 := by
  apply nodeValid_prime [2, 23, 4112094659] ⟨4350596149223, 5, [(2, 1), (23, 2), (4112094659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_4112094659
  · decide +kernel

theorem prime_4354125278917 : Nat.Prime 4354125278917 := by
  apply nodeValid_prime [2, 3, 7, 19, 331, 8242141] ⟨4354125278917, 2, [(2, 2), (3, 1), (7, 1), (19, 1), (331, 1), (8242141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_331
    · exact prime_8242141
  · decide +kernel

theorem prime_4354125279107 : Nat.Prime 4354125279107 := by
  apply nodeValid_prime [2, 17, 19, 6740132011] ⟨4354125279107, 2, [(2, 1), (17, 1), (19, 1), (6740132011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_6740132011
  · decide +kernel

theorem prime_4354125326609 : Nat.Prime 4354125326609 := by
  apply nodeValid_prime [2, 5119, 53161327] ⟨4354125326609, 3, [(2, 4), (5119, 1), (53161327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5119
    · exact prime_53161327
  · decide +kernel

theorem prime_4357656476573 : Nat.Prime 4357656476573 := by
  apply nodeValid_prime [2, 7, 17, 71, 439, 41959] ⟨4357656476573, 12, [(2, 2), (7, 2), (17, 1), (71, 1), (439, 1), (41959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_71
    · exact prime_439
    · exact prime_41959
  · decide +kernel

theorem prime_4357656501071 : Nat.Prime 4357656501071 := by
  apply nodeValid_prime [2, 5, 435765650107] ⟨4357656501071, 11, [(2, 1), (5, 1), (435765650107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_435765650107
  · decide +kernel

theorem prime_4357656501127 : Nat.Prime 4357656501127 := by
  apply nodeValid_prime [2, 3, 726276083521] ⟨4357656501127, 3, [(2, 1), (3, 1), (726276083521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_726276083521
  · decide +kernel

theorem prime_4361189563727 : Nat.Prime 4361189563727 := by
  apply nodeValid_prime [2, 53, 251, 163917521] ⟨4361189563727, 5, [(2, 1), (53, 1), (251, 1), (163917521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_251
    · exact prime_163917521
  · decide +kernel

theorem prime_4361189600917 : Nat.Prime 4361189600917 := by
  apply nodeValid_prime [2, 3, 121144155581] ⟨4361189600917, 6, [(2, 2), (3, 2), (121144155581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_121144155581
  · decide +kernel

theorem prime_4361189602963 : Nat.Prime 4361189602963 := by
  apply nodeValid_prime [2, 3, 29, 25064308063] ⟨4361189602963, 2, [(2, 1), (3, 1), (29, 1), (25064308063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_25064308063
  · decide +kernel

theorem prime_4364724518047 : Nat.Prime 4364724518047 := by
  apply nodeValid_prime [2, 3, 367, 701, 942541] ⟨4364724518047, 5, [(2, 1), (3, 2), (367, 1), (701, 1), (942541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_701
    · exact prime_942541
  · decide +kernel

theorem prime_4364724519037 : Nat.Prime 4364724519037 := by
  apply nodeValid_prime [2, 3, 7, 53, 108932927] ⟨4364724519037, 2, [(2, 2), (3, 3), (7, 1), (53, 1), (108932927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_108932927
  · decide +kernel

theorem prime_4364724594931 : Nat.Prime 4364724594931 := by
  apply nodeValid_prime [2, 3, 5, 7, 191, 601, 181063] ⟨4364724594931, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (191, 1), (601, 1), (181063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_191
    · exact prime_601
    · exact prime_181063
  · decide +kernel

theorem prime_4368261568823 : Nat.Prime 4368261568823 := by
  apply nodeValid_prime [2, 2184130784411] ⟨4368261568823, 5, [(2, 1), (2184130784411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2184130784411
  · decide +kernel

theorem prime_4368261582661 : Nat.Prime 4368261582661 := by
  apply nodeValid_prime [2, 3, 5, 1033, 2311, 30497] ⟨4368261582661, 6, [(2, 2), (3, 1), (5, 1), (1033, 1), (2311, 1), (30497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1033
    · exact prime_2311
    · exact prime_30497
  · decide +kernel

theorem prime_4368261585379 : Nat.Prime 4368261585379 := by
  apply nodeValid_prime [2, 3, 728043597563] ⟨4368261585379, 2, [(2, 1), (3, 1), (728043597563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_728043597563
  · decide +kernel

theorem prime_4371800483261 : Nat.Prime 4371800483261 := by
  apply nodeValid_prime [2, 5, 7, 56453, 553153] ⟨4371800483261, 2, [(2, 2), (5, 1), (7, 1), (56453, 1), (553153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_56453
    · exact prime_553153
  · decide +kernel

theorem prime_4371800527583 : Nat.Prime 4371800527583 := by
  apply nodeValid_prime [2, 245681, 8897311] ⟨4371800527583, 5, [(2, 1), (245681, 1), (8897311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_245681
    · exact prime_8897311
  · decide +kernel

theorem prime_4371800527949 : Nat.Prime 4371800527949 := by
  apply nodeValid_prime [2, 7, 9137, 17088293] ⟨4371800527949, 3, [(2, 2), (7, 1), (9137, 1), (17088293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9137
    · exact prime_17088293
  · decide +kernel

theorem prime_4375341305117 : Nat.Prime 4375341305117 := by
  apply nodeValid_prime [2, 17, 9133, 7045139] ⟨4375341305117, 2, [(2, 2), (17, 1), (9133, 1), (7045139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9133
    · exact prime_7045139
  · decide +kernel

theorem prime_4375341305207 : Nat.Prime 4375341305207 := by
  apply nodeValid_prime [2, 2657, 19219, 42841] ⟨4375341305207, 5, [(2, 1), (2657, 1), (19219, 1), (42841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2657
    · exact prime_19219
    · exact prime_42841
  · decide +kernel

theorem prime_4375341334753 : Nat.Prime 4375341334753 := by
  apply nodeValid_prime [2, 3, 43, 16927, 62617] ⟨4375341334753, 10, [(2, 5), (3, 1), (43, 1), (16927, 1), (62617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_16927
    · exact prime_62617
  · decide +kernel

theorem prime_4378884125821 : Nat.Prime 4378884125821 := by
  apply nodeValid_prime [2, 3, 5, 23, 3173104439] ⟨4378884125821, 6, [(2, 2), (3, 1), (5, 1), (23, 1), (3173104439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_3173104439
  · decide +kernel

theorem prime_4378884148391 : Nat.Prime 4378884148391 := by
  apply nodeValid_prime [2, 5, 53, 271, 30487253] ⟨4378884148391, 7, [(2, 1), (5, 1), (53, 1), (271, 1), (30487253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_271
    · exact prime_30487253
  · decide +kernel

theorem prime_4378884149449 : Nat.Prime 4378884149449 := by
  apply nodeValid_prime [2, 3, 73, 277707011] ⟨4378884149449, 7, [(2, 3), (3, 3), (73, 1), (277707011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_277707011
  · decide +kernel

theorem prime_4382428814219 : Nat.Prime 4382428814219 := by
  apply nodeValid_prime [2, 7, 13, 701, 4363, 7873] ⟨4382428814219, 2, [(2, 1), (7, 1), (13, 1), (701, 1), (4363, 1), (7873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_701
    · exact prime_4363
    · exact prime_7873
  · decide +kernel

theorem prime_4382428814263 : Nat.Prime 4382428814263 := by
  apply nodeValid_prime [2, 3, 81156089153] ⟨4382428814263, 6, [(2, 1), (3, 3), (81156089153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_81156089153
  · decide +kernel

theorem prime_4382428859687 : Nat.Prime 4382428859687 := by
  apply nodeValid_prime [2, 79, 57191, 484987] ⟨4382428859687, 5, [(2, 1), (79, 1), (57191, 1), (484987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_57191
    · exact prime_484987
  · decide +kernel

theorem prime_4385975478961 : Nat.Prime 4385975478961 := by
  apply nodeValid_prime [2, 3, 5, 53, 59, 61, 149, 643] ⟨4385975478961, 14, [(2, 4), (3, 1), (5, 1), (53, 1), (59, 1), (61, 1), (149, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_59
    · exact prime_61
    · exact prime_149
    · exact prime_643
  · decide +kernel

theorem prime_4385975480083 : Nat.Prime 4385975480083 := by
  apply nodeValid_prime [2, 3, 7, 82529, 421783] ⟨4385975480083, 3, [(2, 1), (3, 2), (7, 1), (82529, 1), (421783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_82529
    · exact prime_421783
  · decide +kernel

theorem prime_4385975528677 : Nat.Prime 4385975528677 := by
  apply nodeValid_prime [2, 3, 7, 52213994389] ⟨4385975528677, 5, [(2, 2), (3, 1), (7, 1), (52213994389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_52213994389
  · decide +kernel

theorem prime_4389524130461 : Nat.Prime 4389524130461 := by
  apply nodeValid_prime [2, 5, 7, 21101, 1485889] ⟨4389524130461, 2, [(2, 2), (5, 1), (7, 1), (21101, 1), (1485889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_21101
    · exact prime_1485889
  · decide +kernel

theorem prime_4389524154401 : Nat.Prime 4389524154401 := by
  apply nodeValid_prime [2, 5, 7, 11, 17, 281, 2131] ⟨4389524154401, 3, [(2, 5), (5, 2), (7, 2), (11, 1), (17, 1), (281, 1), (2131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_281
    · exact prime_2131
  · decide +kernel

theorem prime_4389524155039 : Nat.Prime 4389524155039 := by
  apply nodeValid_prime [2, 3, 11, 23, 37, 107, 730399] ⟨4389524155039, 3, [(2, 1), (3, 1), (11, 1), (23, 1), (37, 1), (107, 1), (730399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_37
    · exact prime_107
    · exact prime_730399
  · decide +kernel

theorem prime_4393074680147 : Nat.Prime 4393074680147 := by
  apply nodeValid_prime [2, 139, 15802426907] ⟨4393074680147, 2, [(2, 1), (139, 1), (15802426907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_15802426907
  · decide +kernel

theorem prime_4393074730589 : Nat.Prime 4393074730589 := by
  apply nodeValid_prime [2, 23, 47750812289] ⟨4393074730589, 2, [(2, 2), (23, 1), (47750812289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47750812289
  · decide +kernel

theorem prime_4393074730943 : Nat.Prime 4393074730943 := by
  apply nodeValid_prime [2, 79, 6217, 4472297] ⟨4393074730943, 5, [(2, 1), (79, 1), (6217, 1), (4472297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_6217
    · exact prime_4472297
  · decide +kernel

theorem prime_4396627174391 : Nat.Prime 4396627174391 := by
  apply nodeValid_prime [2, 5, 11, 37, 1080252377] ⟨4396627174391, 7, [(2, 1), (5, 1), (11, 1), (37, 1), (1080252377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
    · exact prime_1080252377
  · decide +kernel

theorem prime_4396627193639 : Nat.Prime 4396627193639 := by
  apply nodeValid_prime [2, 10891, 201846809] ⟨4396627193639, 7, [(2, 1), (10891, 1), (201846809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10891
    · exact prime_201846809
  · decide +kernel

theorem prime_4396627195547 : Nat.Prime 4396627195547 := by
  apply nodeValid_prime [2, 73, 30113884901] ⟨4396627195547, 2, [(2, 1), (73, 1), (30113884901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_30113884901
  · decide +kernel

theorem prime_4400181610633 : Nat.Prime 4400181610633 := by
  apply nodeValid_prime [2, 3, 173, 1597, 221201] ⟨4400181610633, 5, [(2, 3), (3, 2), (173, 1), (1597, 1), (221201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_1597
    · exact prime_221201
  · decide +kernel

theorem prime_4400181705961 : Nat.Prime 4400181705961 := by
  apply nodeValid_prime [2, 3, 5, 19, 263, 2446013] ⟨4400181705961, 7, [(2, 3), (3, 2), (5, 1), (19, 1), (263, 1), (2446013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_263
    · exact prime_2446013
  · decide +kernel

theorem prime_4400181706421 : Nat.Prime 4400181706421 := by
  apply nodeValid_prime [2, 5, 421, 522586901] ⟨4400181706421, 2, [(2, 2), (5, 1), (421, 1), (522586901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_421
    · exact prime_522586901
  · decide +kernel

theorem prime_4403737876099 : Nat.Prime 4403737876099 := by
  apply nodeValid_prime [2, 3, 11, 138577, 481489] ⟨4403737876099, 3, [(2, 1), (3, 1), (11, 1), (138577, 1), (481489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_138577
    · exact prime_481489
  · decide +kernel

theorem prime_4403737876469 : Nat.Prime 4403737876469 := by
  apply nodeValid_prime [2, 7, 26959, 5833909] ⟨4403737876469, 2, [(2, 2), (7, 1), (26959, 1), (5833909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_26959
    · exact prime_5833909
  · decide +kernel

theorem prime_4403737989697 : Nat.Prime 4403737989697 := by
  apply nodeValid_prime [2, 3, 53, 59, 7334869] ⟨4403737989697, 5, [(2, 6), (3, 1), (53, 1), (59, 1), (7334869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_59
    · exact prime_7334869
  · decide +kernel

end Sude.Lucas.Generated
