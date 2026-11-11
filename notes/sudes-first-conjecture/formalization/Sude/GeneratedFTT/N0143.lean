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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0082
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0125

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7907 : Nat.Prime 7907 := by
  apply nodeValid_prime [2, 59, 67] ⟨7907, 2, [(2, 1), (59, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_67
  · decide +kernel

theorem prime_15511 : Nat.Prime 15511 := by
  apply nodeValid_prime [2, 3, 5, 11, 47] ⟨15511, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_16063 : Nat.Prime 16063 := by
  apply nodeValid_prime [2, 3, 2677] ⟨16063, 5, [(2, 1), (3, 1), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2677
  · decide +kernel

theorem prime_22259 : Nat.Prime 22259 := by
  apply nodeValid_prime [2, 31, 359] ⟨22259, 2, [(2, 1), (31, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_359
  · decide +kernel

theorem prime_23039 : Nat.Prime 23039 := by
  apply nodeValid_prime [2, 11519] ⟨23039, 7, [(2, 1), (11519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11519
  · decide +kernel

theorem prime_32191 : Nat.Prime 32191 := by
  apply nodeValid_prime [2, 3, 5, 29, 37] ⟨32191, 6, [(2, 1), (3, 1), (5, 1), (29, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_37
  · decide +kernel

theorem prime_34693 : Nat.Prime 34693 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨34693, 6, [(2, 2), (3, 1), (7, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_36931 : Nat.Prime 36931 := by
  apply nodeValid_prime [2, 3, 5, 1231] ⟨36931, 2, [(2, 1), (3, 1), (5, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1231
  · decide +kernel

theorem prime_39023 : Nat.Prime 39023 := by
  apply nodeValid_prime [2, 109, 179] ⟨39023, 5, [(2, 1), (109, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_179
  · decide +kernel

theorem prime_41911 : Nat.Prime 41911 := by
  apply nodeValid_prime [2, 3, 5, 11, 127] ⟨41911, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_127
  · decide +kernel

theorem prime_42043 : Nat.Prime 42043 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨42043, 5, [(2, 1), (3, 1), (7, 2), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_44519 : Nat.Prime 44519 := by
  apply nodeValid_prime [2, 22259] ⟨44519, 13, [(2, 1), (22259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22259
  · decide +kernel

theorem prime_45869 : Nat.Prime 45869 := by
  apply nodeValid_prime [2, 11467] ⟨45869, 2, [(2, 2), (11467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11467
  · decide +kernel

theorem prime_49991 : Nat.Prime 49991 := by
  apply nodeValid_prime [2, 5, 4999] ⟨49991, 7, [(2, 1), (5, 1), (4999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4999
  · decide +kernel

theorem prime_53299 : Nat.Prime 53299 := by
  apply nodeValid_prime [2, 3, 7, 47] ⟨53299, 2, [(2, 1), (3, 4), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_55901 : Nat.Prime 55901 := by
  apply nodeValid_prime [2, 5, 13, 43] ⟨55901, 2, [(2, 2), (5, 2), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_57529 : Nat.Prime 57529 := by
  apply nodeValid_prime [2, 3, 17, 47] ⟨57529, 7, [(2, 3), (3, 2), (17, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_67709 : Nat.Prime 67709 := by
  apply nodeValid_prime [2, 16927] ⟨67709, 2, [(2, 2), (16927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16927
  · decide +kernel

theorem prime_69661 : Nat.Prime 69661 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨69661, 6, [(2, 2), (3, 4), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_86939 : Nat.Prime 86939 := by
  apply nodeValid_prime [2, 17, 2557] ⟨86939, 2, [(2, 1), (17, 1), (2557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2557
  · decide +kernel

theorem prime_94543 : Nat.Prime 94543 := by
  apply nodeValid_prime [2, 3, 7, 2251] ⟨94543, 3, [(2, 1), (3, 1), (7, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2251
  · decide +kernel

theorem prime_133087 : Nat.Prime 133087 := by
  apply nodeValid_prime [2, 3, 41, 541] ⟨133087, 5, [(2, 1), (3, 1), (41, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_541
  · decide +kernel

theorem prime_140869 : Nat.Prime 140869 := by
  apply nodeValid_prime [2, 3, 7, 13, 43] ⟨140869, 10, [(2, 2), (3, 2), (7, 1), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_145459 : Nat.Prime 145459 := by
  apply nodeValid_prime [2, 3, 8081] ⟨145459, 2, [(2, 1), (3, 2), (8081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8081
  · decide +kernel

theorem prime_156677 : Nat.Prime 156677 := by
  apply nodeValid_prime [2, 13, 23, 131] ⟨156677, 2, [(2, 2), (13, 1), (23, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_131
  · decide +kernel

theorem prime_171491 : Nat.Prime 171491 := by
  apply nodeValid_prime [2, 5, 11, 1559] ⟨171491, 2, [(2, 1), (5, 1), (11, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1559
  · decide +kernel

theorem prime_195907 : Nat.Prime 195907 := by
  apply nodeValid_prime [2, 3, 103, 317] ⟨195907, 2, [(2, 1), (3, 1), (103, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_317
  · decide +kernel

theorem prime_206237 : Nat.Prime 206237 := by
  apply nodeValid_prime [2, 47, 1097] ⟨206237, 2, [(2, 2), (47, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1097
  · decide +kernel

theorem prime_271217 : Nat.Prime 271217 := by
  apply nodeValid_prime [2, 11, 23, 67] ⟨271217, 3, [(2, 4), (11, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_283027 : Nat.Prime 283027 := by
  apply nodeValid_prime [2, 3, 43, 1097] ⟨283027, 2, [(2, 1), (3, 1), (43, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1097
  · decide +kernel

theorem prime_364657 : Nat.Prime 364657 := by
  apply nodeValid_prime [2, 3, 71, 107] ⟨364657, 5, [(2, 4), (3, 1), (71, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_107
  · decide +kernel

theorem prime_401707 : Nat.Prime 401707 := by
  apply nodeValid_prime [2, 3, 43, 173] ⟨401707, 12, [(2, 1), (3, 3), (43, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_173
  · decide +kernel

theorem prime_435881 : Nat.Prime 435881 := by
  apply nodeValid_prime [2, 5, 17, 641] ⟨435881, 3, [(2, 3), (5, 1), (17, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_641
  · decide +kernel

theorem prime_455647 : Nat.Prime 455647 := by
  apply nodeValid_prime [2, 3, 75941] ⟨455647, 3, [(2, 1), (3, 1), (75941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75941
  · decide +kernel

theorem prime_458039 : Nat.Prime 458039 := by
  apply nodeValid_prime [2, 7, 32717] ⟨458039, 7, [(2, 1), (7, 1), (32717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_32717
  · decide +kernel

theorem prime_498613 : Nat.Prime 498613 := by
  apply nodeValid_prime [2, 3, 37, 1123] ⟨498613, 2, [(2, 2), (3, 1), (37, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1123
  · decide +kernel

theorem prime_541589 : Nat.Prime 541589 := by
  apply nodeValid_prime [2, 71, 1907] ⟨541589, 2, [(2, 2), (71, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1907
  · decide +kernel

theorem prime_619019 : Nat.Prime 619019 := by
  apply nodeValid_prime [2, 41, 7549] ⟨619019, 2, [(2, 1), (41, 1), (7549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_7549
  · decide +kernel

theorem prime_839071 : Nat.Prime 839071 := by
  apply nodeValid_prime [2, 3, 5, 9323] ⟨839071, 3, [(2, 1), (3, 2), (5, 1), (9323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9323
  · decide +kernel

theorem prime_917381 : Nat.Prime 917381 := by
  apply nodeValid_prime [2, 5, 45869] ⟨917381, 3, [(2, 2), (5, 1), (45869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_45869
  · decide +kernel

theorem prime_1142129 : Nat.Prime 1142129 := by
  apply nodeValid_prime [2, 13, 17, 19] ⟨1142129, 3, [(2, 4), (13, 1), (17, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_1458629 : Nat.Prime 1458629 := by
  apply nodeValid_prime [2, 364657] ⟨1458629, 2, [(2, 2), (364657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_364657
  · decide +kernel

theorem prime_1714621 : Nat.Prime 1714621 := by
  apply nodeValid_prime [2, 3, 5, 17, 41] ⟨1714621, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_1785401 : Nat.Prime 1785401 := by
  apply nodeValid_prime [2, 5, 79, 113] ⟨1785401, 3, [(2, 3), (5, 2), (79, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_113
  · decide +kernel

theorem prime_2089831 : Nat.Prime 2089831 := by
  apply nodeValid_prime [2, 3, 5, 69661] ⟨2089831, 3, [(2, 1), (3, 1), (5, 1), (69661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_69661
  · decide +kernel

theorem prime_2618263 : Nat.Prime 2618263 := by
  apply nodeValid_prime [2, 3, 145459] ⟨2618263, 5, [(2, 1), (3, 2), (145459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_145459
  · decide +kernel

theorem prime_2806757 : Nat.Prime 2806757 := by
  apply nodeValid_prime [2, 19, 36931] ⟨2806757, 2, [(2, 2), (19, 1), (36931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_36931
  · decide +kernel

theorem prime_2920321 : Nat.Prime 2920321 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨2920321, 7, [(2, 7), (3, 3), (5, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_3028379 : Nat.Prime 3028379 := by
  apply nodeValid_prime [2, 167, 9067] ⟨3028379, 2, [(2, 1), (167, 1), (9067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_9067
  · decide +kernel

theorem prime_4561723 : Nat.Prime 4561723 := by
  apply nodeValid_prime [2, 3, 11, 23039] ⟨4561723, 3, [(2, 1), (3, 2), (11, 1), (23039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23039
  · decide +kernel

theorem prime_5094487 : Nat.Prime 5094487 := by
  apply nodeValid_prime [2, 3, 283027] ⟨5094487, 5, [(2, 1), (3, 2), (283027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283027
  · decide +kernel

theorem prime_5431819 : Nat.Prime 5431819 := by
  apply nodeValid_prime [2, 3, 7, 23, 5623] ⟨5431819, 2, [(2, 1), (3, 1), (7, 1), (23, 1), (5623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_5623
  · decide +kernel

theorem prime_5477209 : Nat.Prime 5477209 := by
  apply nodeValid_prime [2, 3, 11, 20747] ⟨5477209, 7, [(2, 3), (3, 1), (11, 1), (20747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_20747
  · decide +kernel

theorem prime_6040897 : Nat.Prime 6040897 := by
  apply nodeValid_prime [2, 3, 73, 431] ⟨6040897, 5, [(2, 6), (3, 1), (73, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_431
  · decide +kernel

theorem prime_7082021 : Nat.Prime 7082021 := by
  apply nodeValid_prime [2, 5, 11, 32191] ⟨7082021, 2, [(2, 2), (5, 1), (11, 1), (32191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_32191
  · decide +kernel

theorem prime_8206201 : Nat.Prime 8206201 := by
  apply nodeValid_prime [2, 3, 5, 47, 97] ⟨8206201, 21, [(2, 3), (3, 2), (5, 2), (47, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_97
  · decide +kernel

theorem prime_8995163 : Nat.Prime 8995163 := by
  apply nodeValid_prime [2, 11, 23, 29, 613] ⟨8995163, 2, [(2, 1), (11, 1), (23, 1), (29, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_29
    · exact prime_613
  · decide +kernel

theorem prime_8997869 : Nat.Prime 8997869 := by
  apply nodeValid_prime [2, 11, 19, 47, 229] ⟨8997869, 2, [(2, 2), (11, 1), (19, 1), (47, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_47
    · exact prime_229
  · decide +kernel

theorem prime_10644859 : Nat.Prime 10644859 := by
  apply nodeValid_prime [2, 3, 7, 149] ⟨10644859, 7, [(2, 1), (3, 6), (7, 2), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_14643229 : Nat.Prime 14643229 := by
  apply nodeValid_prime [2, 3, 167, 7307] ⟨14643229, 7, [(2, 2), (3, 1), (167, 1), (7307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_7307
  · decide +kernel

theorem prime_17217653 : Nat.Prime 17217653 := by
  apply nodeValid_prime [2, 139, 173, 179] ⟨17217653, 2, [(2, 2), (139, 1), (173, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_173
    · exact prime_179
  · decide +kernel

theorem prime_22321253 : Nat.Prime 22321253 := by
  apply nodeValid_prime [2, 97, 57529] ⟨22321253, 2, [(2, 2), (97, 1), (57529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_57529
  · decide +kernel

theorem prime_23110589 : Nat.Prime 23110589 := by
  apply nodeValid_prime [2, 947, 6101] ⟨23110589, 2, [(2, 2), (947, 1), (6101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_947
    · exact prime_6101
  · decide +kernel

theorem prime_23782573 : Nat.Prime 23782573 := by
  apply nodeValid_prime [2, 3, 11, 6673] ⟨23782573, 2, [(2, 2), (3, 4), (11, 1), (6673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6673
  · decide +kernel

theorem prime_26032577 : Nat.Prime 26032577 := by
  apply nodeValid_prime [2, 17, 71, 337] ⟨26032577, 3, [(2, 6), (17, 1), (71, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_337
  · decide +kernel

theorem prime_35708021 : Nat.Prime 35708021 := by
  apply nodeValid_prime [2, 5, 1785401] ⟨35708021, 2, [(2, 2), (5, 1), (1785401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1785401
  · decide +kernel

theorem prime_36245383 : Nat.Prime 36245383 := by
  apply nodeValid_prime [2, 3, 6040897] ⟨36245383, 3, [(2, 1), (3, 1), (6040897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6040897
  · decide +kernel

theorem prime_43194533 : Nat.Prime 43194533 := by
  apply nodeValid_prime [2, 31, 43, 8101] ⟨43194533, 2, [(2, 2), (31, 1), (43, 1), (8101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_8101
  · decide +kernel

theorem prime_67587437 : Nat.Prime 67587437 := by
  apply nodeValid_prime [2, 7, 1117, 2161] ⟨67587437, 5, [(2, 2), (7, 1), (1117, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1117
    · exact prime_2161
  · decide +kernel

theorem prime_82201297 : Nat.Prime 82201297 := by
  apply nodeValid_prime [2, 3, 19, 173, 521] ⟨82201297, 7, [(2, 4), (3, 1), (19, 1), (173, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_173
    · exact prime_521
  · decide +kernel

theorem prime_86725997 : Nat.Prime 86725997 := by
  apply nodeValid_prime [2, 7, 409, 7573] ⟨86725997, 2, [(2, 2), (7, 1), (409, 1), (7573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_409
    · exact prime_7573
  · decide +kernel

theorem prime_98474413 : Nat.Prime 98474413 := by
  apply nodeValid_prime [2, 3, 8206201] ⟨98474413, 2, [(2, 2), (3, 1), (8206201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8206201
  · decide +kernel

theorem prime_138933203 : Nat.Prime 138933203 := by
  apply nodeValid_prime [2, 23, 83, 36389] ⟨138933203, 2, [(2, 1), (23, 1), (83, 1), (36389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_83
    · exact prime_36389
  · decide +kernel

theorem prime_153615949 : Nat.Prime 153615949 := by
  apply nodeValid_prime [2, 3, 229, 55901] ⟨153615949, 2, [(2, 2), (3, 1), (229, 1), (55901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_55901
  · decide +kernel

theorem prime_208260617 : Nat.Prime 208260617 := by
  apply nodeValid_prime [2, 26032577] ⟨208260617, 3, [(2, 3), (26032577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26032577
  · decide +kernel

theorem prime_226370303 : Nat.Prime 226370303 := by
  apply nodeValid_prime [2, 227, 498613] ⟨226370303, 5, [(2, 1), (227, 1), (498613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_498613
  · decide +kernel

theorem prime_285909161 : Nat.Prime 285909161 := by
  apply nodeValid_prime [2, 5, 1423, 5023] ⟨285909161, 3, [(2, 3), (5, 1), (1423, 1), (5023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1423
    · exact prime_5023
  · decide +kernel

theorem prime_343955201 : Nat.Prime 343955201 := by
  apply nodeValid_prime [2, 5, 223, 241] ⟨343955201, 11, [(2, 8), (5, 2), (223, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_223
    · exact prime_241
  · decide +kernel

theorem prime_444022619 : Nat.Prime 444022619 := by
  apply nodeValid_prime [2, 13, 109, 156677] ⟨444022619, 2, [(2, 1), (13, 1), (109, 1), (156677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_109
    · exact prime_156677
  · decide +kernel

theorem prime_467251361 : Nat.Prime 467251361 := by
  apply nodeValid_prime [2, 5, 2920321] ⟨467251361, 3, [(2, 5), (5, 1), (2920321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2920321
  · decide +kernel

theorem prime_498415633 : Nat.Prime 498415633 := by
  apply nodeValid_prime [2, 3, 11, 13, 72613] ⟨498415633, 35, [(2, 4), (3, 1), (11, 1), (13, 1), (72613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_72613
  · decide +kernel

theorem prime_585005761 : Nat.Prime 585005761 := by
  apply nodeValid_prime [2, 3, 5, 67709] ⟨585005761, 13, [(2, 6), (3, 3), (5, 1), (67709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67709
  · decide +kernel

theorem prime_687910403 : Nat.Prime 687910403 := by
  apply nodeValid_prime [2, 343955201] ⟨687910403, 2, [(2, 1), (343955201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_343955201
  · decide +kernel

theorem prime_718311647 : Nat.Prime 718311647 := by
  apply nodeValid_prime [2, 13, 43, 193, 3329] ⟨718311647, 5, [(2, 1), (13, 1), (43, 1), (193, 1), (3329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_193
    · exact prime_3329
  · decide +kernel

theorem prime_803953151 : Nat.Prime 803953151 := by
  apply nodeValid_prime [2, 5, 7, 11, 13, 16063] ⟨803953151, 7, [(2, 1), (5, 2), (7, 1), (11, 1), (13, 1), (16063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_16063
  · decide +kernel

theorem prime_1126249511 : Nat.Prime 1126249511 := by
  apply nodeValid_prime [2, 5, 19, 23, 29, 8887] ⟨1126249511, 19, [(2, 1), (5, 1), (19, 1), (23, 1), (29, 1), (8887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_29
    · exact prime_8887
  · decide +kernel

theorem prime_1146832021 : Nat.Prime 1146832021 := by
  apply nodeValid_prime [2, 3, 5, 19, 37, 53] ⟨1146832021, 21, [(2, 2), (3, 4), (5, 1), (19, 2), (37, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_37
    · exact prime_53
  · decide +kernel

theorem prime_1235545151 : Nat.Prime 1235545151 := by
  apply nodeValid_prime [2, 5, 7, 593, 5953] ⟨1235545151, 7, [(2, 1), (5, 2), (7, 1), (593, 1), (5953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_593
    · exact prime_5953
  · decide +kernel

theorem prime_1788336313 : Nat.Prime 1788336313 := by
  apply nodeValid_prime [2, 3, 7, 10644859] ⟨1788336313, 5, [(2, 3), (3, 1), (7, 1), (10644859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10644859
  · decide +kernel

theorem prime_2600182111 : Nat.Prime 2600182111 := by
  apply nodeValid_prime [2, 3, 5, 19, 4561723] ⟨2600182111, 6, [(2, 1), (3, 1), (5, 1), (19, 1), (4561723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_4561723
  · decide +kernel

theorem prime_4566918259 : Nat.Prime 4566918259 := by
  apply nodeValid_prime [2, 3, 7, 36245383] ⟨4566918259, 10, [(2, 1), (3, 2), (7, 1), (36245383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_36245383
  · decide +kernel

theorem prime_5408242649 : Nat.Prime 5408242649 := by
  apply nodeValid_prime [2, 4799, 140869] ⟨5408242649, 3, [(2, 3), (4799, 1), (140869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4799
    · exact prime_140869
  · decide +kernel

theorem prime_6880992127 : Nat.Prime 6880992127 := by
  apply nodeValid_prime [2, 3, 1146832021] ⟨6880992127, 5, [(2, 1), (3, 1), (1146832021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1146832021
  · decide +kernel

theorem prime_8080293587 : Nat.Prime 8080293587 := by
  apply nodeValid_prime [2, 181, 22321253] ⟨8080293587, 2, [(2, 1), (181, 1), (22321253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_22321253
  · decide +kernel

theorem prime_8329659391 : Nat.Prime 8329659391 := by
  apply nodeValid_prime [2, 3, 5, 13, 31, 179, 1283] ⟨8329659391, 7, [(2, 1), (3, 2), (5, 1), (13, 1), (31, 1), (179, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_179
    · exact prime_1283
  · decide +kernel

theorem prime_8818786211 : Nat.Prime 8818786211 := by
  apply nodeValid_prime [2, 5, 13, 17, 1693, 2357] ⟨8818786211, 6, [(2, 1), (5, 1), (13, 1), (17, 1), (1693, 1), (2357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_1693
    · exact prime_2357
  · decide +kernel

theorem prime_10953135293 : Nat.Prime 10953135293 := by
  apply nodeValid_prime [2, 11, 17, 14643229] ⟨10953135293, 2, [(2, 2), (11, 1), (17, 1), (14643229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_14643229
  · decide +kernel

theorem prime_13514994133 : Nat.Prime 13514994133 := by
  apply nodeValid_prime [2, 3, 1126249511] ⟨13514994133, 5, [(2, 2), (3, 1), (1126249511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1126249511
  · decide +kernel

theorem prime_14251055419 : Nat.Prime 14251055419 := by
  apply nodeValid_prime [2, 3, 1279, 619019] ⟨14251055419, 2, [(2, 1), (3, 2), (1279, 1), (619019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
    · exact prime_619019
  · decide +kernel

theorem prime_18267673037 : Nat.Prime 18267673037 := by
  apply nodeValid_prime [2, 4566918259] ⟨18267673037, 2, [(2, 2), (4566918259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4566918259
  · decide +kernel

theorem prime_21093342653 : Nat.Prime 21093342653 := by
  apply nodeValid_prime [2, 41, 401, 7823] ⟨21093342653, 2, [(2, 2), (41, 2), (401, 1), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_401
    · exact prime_7823
  · decide +kernel

theorem prime_21446479469 : Nat.Prime 21446479469 := by
  apply nodeValid_prime [2, 53, 59, 1714621] ⟨21446479469, 2, [(2, 2), (53, 1), (59, 1), (1714621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_59
    · exact prime_1714621
  · decide +kernel

theorem prime_22815895241 : Nat.Prime 22815895241 := by
  apply nodeValid_prime [2, 5, 13567, 42043] ⟨22815895241, 3, [(2, 3), (5, 1), (13567, 1), (42043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13567
    · exact prime_42043
  · decide +kernel

theorem prime_46392338017 : Nat.Prime 46392338017 := by
  apply nodeValid_prime [2, 3, 401, 401707] ⟨46392338017, 5, [(2, 5), (3, 2), (401, 1), (401707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_401707
  · decide +kernel

theorem prime_73469841259 : Nat.Prime 73469841259 := by
  apply nodeValid_prime [2, 3, 11, 29, 997, 38501] ⟨73469841259, 10, [(2, 1), (3, 1), (11, 1), (29, 1), (997, 1), (38501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_997
    · exact prime_38501
  · decide +kernel

theorem prime_75245572991 : Nat.Prime 75245572991 := by
  apply nodeValid_prime [2, 5, 7, 211, 5094487] ⟨75245572991, 7, [(2, 1), (5, 1), (7, 1), (211, 1), (5094487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_211
    · exact prime_5094487
  · decide +kernel

theorem prime_133274550257 : Nat.Prime 133274550257 := by
  apply nodeValid_prime [2, 8329659391] ⟨133274550257, 3, [(2, 4), (8329659391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8329659391
  · decide +kernel

theorem prime_150491145983 : Nat.Prime 150491145983 := by
  apply nodeValid_prime [2, 75245572991] ⟨150491145983, 5, [(2, 1), (75245572991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_75245572991
  · decide +kernel

theorem prime_156123412457 : Nat.Prime 156123412457 := by
  apply nodeValid_prime [2, 11, 37, 947, 4603] ⟨156123412457, 3, [(2, 3), (11, 2), (37, 1), (947, 1), (4603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_947
    · exact prime_4603
  · decide +kernel

theorem prime_162247279471 : Nat.Prime 162247279471 := by
  apply nodeValid_prime [2, 3, 5, 5408242649] ⟨162247279471, 7, [(2, 1), (3, 1), (5, 1), (5408242649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5408242649
  · decide +kernel

theorem prime_209157527591 : Nat.Prime 209157527591 := by
  apply nodeValid_prime [2, 5, 11, 8461, 224729] ⟨209157527591, 19, [(2, 1), (5, 1), (11, 1), (8461, 1), (224729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_8461
    · exact prime_224729
  · decide +kernel

theorem prime_530922159653 : Nat.Prime 530922159653 := by
  apply nodeValid_prime [2, 5581, 23782573] ⟨530922159653, 2, [(2, 2), (5581, 1), (23782573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5581
    · exact prime_23782573
  · decide +kernel

theorem prime_1241355323347 : Nat.Prime 1241355323347 := by
  apply nodeValid_prime [2, 3, 41, 929, 5431819] ⟨1241355323347, 2, [(2, 1), (3, 1), (41, 1), (929, 1), (5431819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_929
    · exact prime_5431819
  · decide +kernel

theorem prime_1853161818913 : Nat.Prime 1853161818913 := by
  apply nodeValid_prime [2, 3, 3079, 2089831] ⟨1853161818913, 5, [(2, 5), (3, 2), (3079, 1), (2089831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3079
    · exact prime_2089831
  · decide +kernel

theorem prime_3721527781043 : Nat.Prime 3721527781043 := by
  apply nodeValid_prime [2, 211, 8818786211] ⟨3721527781043, 2, [(2, 1), (211, 1), (8818786211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_8818786211
  · decide +kernel

theorem prime_7407587290721 : Nat.Prime 7407587290721 := by
  apply nodeValid_prime [2, 5, 23, 2399, 839071] ⟨7407587290721, 3, [(2, 5), (5, 1), (23, 1), (2399, 1), (839071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_2399
    · exact prime_839071
  · decide +kernel

theorem prime_7407587290879 : Nat.Prime 7407587290879 := by
  apply nodeValid_prime [2, 3, 31, 67763, 195907] ⟨7407587290879, 3, [(2, 1), (3, 2), (31, 1), (67763, 1), (195907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_67763
    · exact prime_195907
  · decide +kernel

theorem prime_7407587460887 : Nat.Prime 7407587460887 := by
  apply nodeValid_prime [2, 577, 2287, 2806757] ⟨7407587460887, 5, [(2, 1), (577, 1), (2287, 1), (2806757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_2287
    · exact prime_2806757
  · decide +kernel

theorem prime_7412647275479 : Nat.Prime 7412647275479 := by
  apply nodeValid_prime [2, 167, 1289, 17217653] ⟨7412647275479, 17, [(2, 1), (167, 1), (1289, 1), (17217653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_1289
    · exact prime_17217653
  · decide +kernel

theorem prime_7412647275653 : Nat.Prime 7412647275653 := by
  apply nodeValid_prime [2, 1853161818913] ⟨7412647275653, 2, [(2, 2), (1853161818913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1853161818913
  · decide +kernel

theorem prime_7412647329121 : Nat.Prime 7412647329121 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 4127, 8297] ⟨7412647329121, 13, [(2, 5), (3, 1), (5, 1), (11, 1), (41, 1), (4127, 1), (8297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_4127
    · exact prime_8297
  · decide +kernel

theorem prime_7417709512867 : Nat.Prime 7417709512867 := by
  apply nodeValid_prime [2, 3, 17, 8080293587] ⟨7417709512867, 11, [(2, 1), (3, 3), (17, 1), (8080293587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8080293587
  · decide +kernel

theorem prime_7417709512907 : Nat.Prime 7417709512907 := by
  apply nodeValid_prime [2, 7, 11, 6880992127] ⟨7417709512907, 5, [(2, 1), (7, 2), (11, 1), (6880992127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_6880992127
  · decide +kernel

theorem prime_7417709528941 : Nat.Prime 7417709528941 := by
  apply nodeValid_prime [2, 3, 5, 94543, 435881] ⟨7417709528941, 2, [(2, 2), (3, 2), (5, 1), (94543, 1), (435881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_94543
    · exact prime_435881
  · decide +kernel

theorem prime_7422774035773 : Nat.Prime 7422774035773 := by
  apply nodeValid_prime [2, 3, 541589, 1142129] ⟨7422774035773, 7, [(2, 2), (3, 1), (541589, 1), (1142129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_541589
    · exact prime_1142129
  · decide +kernel

theorem prime_7422774035813 : Nat.Prime 7422774035813 := by
  apply nodeValid_prime [2, 206237, 8997869] ⟨7422774035813, 2, [(2, 2), (206237, 1), (8997869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_206237
    · exact prime_8997869
  · decide +kernel

theorem prime_7422774082721 : Nat.Prime 7422774082721 := by
  apply nodeValid_prime [2, 5, 46392338017] ⟨7422774082721, 3, [(2, 5), (5, 1), (46392338017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_46392338017
  · decide +kernel

theorem prime_7427840929393 : Nat.Prime 7427840929393 := by
  apply nodeValid_prime [2, 3, 13, 17, 53, 139, 5591] ⟨7427840929393, 5, [(2, 4), (3, 1), (13, 1), (17, 2), (53, 1), (139, 1), (5591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_53
    · exact prime_139
    · exact prime_5591
  · decide +kernel

theorem prime_7427840930833 : Nat.Prime 7427840930833 := by
  apply nodeValid_prime [2, 3, 7, 61, 8647, 41911] ⟨7427840930833, 19, [(2, 4), (3, 1), (7, 1), (61, 1), (8647, 1), (41911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_8647
    · exact prime_41911
  · decide +kernel

theorem prime_7427840981459 : Nat.Prime 7427840981459 := by
  apply nodeValid_prime [2, 251, 503, 977, 30109] ⟨7427840981459, 2, [(2, 1), (251, 1), (503, 1), (977, 1), (30109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_503
    · exact prime_977
    · exact prime_30109
  · decide +kernel

theorem prime_7432910225677 : Nat.Prime 7432910225677 := by
  apply nodeValid_prime [2, 3, 13, 23, 15511, 44519] ⟨7432910225677, 2, [(2, 2), (3, 2), (13, 1), (23, 1), (15511, 1), (44519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_15511
    · exact prime_44519
  · decide +kernel

theorem prime_7432910235143 : Nat.Prime 7432910235143 := by
  apply nodeValid_prime [2, 7, 530922159653] ⟨7432910235143, 5, [(2, 1), (7, 1), (530922159653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_530922159653
  · decide +kernel

theorem prime_7432910235319 : Nat.Prime 7432910235319 := by
  apply nodeValid_prime [2, 3, 34693, 35708021] ⟨7432910235319, 3, [(2, 1), (3, 1), (34693, 1), (35708021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34693
    · exact prime_35708021
  · decide +kernel

theorem prime_7437981809021 : Nat.Prime 7437981809021 := by
  apply nodeValid_prime [2, 5, 7, 43, 1235545151] ⟨7437981809021, 2, [(2, 2), (5, 1), (7, 1), (43, 1), (1235545151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_1235545151
  · decide +kernel

theorem prime_7437981848047 : Nat.Prime 7437981848047 := by
  apply nodeValid_prime [2, 3, 73, 373, 2543, 17903] ⟨7437981848047, 3, [(2, 1), (3, 1), (73, 1), (373, 1), (2543, 1), (17903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_373
    · exact prime_2543
    · exact prime_17903
  · decide +kernel

theorem prime_7437981848567 : Nat.Prime 7437981848567 := by
  apply nodeValid_prime [2, 163, 22815895241] ⟨7437981848567, 5, [(2, 1), (163, 1), (22815895241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_22815895241
  · decide +kernel

theorem prime_7443055562087 : Nat.Prime 7443055562087 := by
  apply nodeValid_prime [2, 3721527781043] ⟨7443055562087, 5, [(2, 1), (3721527781043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3721527781043
  · decide +kernel

theorem prime_7443055562641 : Nat.Prime 7443055562641 := by
  apply nodeValid_prime [2, 3, 5, 137, 226370303] ⟨7443055562641, 11, [(2, 4), (3, 1), (5, 1), (137, 1), (226370303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_226370303
  · decide +kernel

theorem prime_7443055734707 : Nat.Prime 7443055734707 := by
  apply nodeValid_prime [2, 2081, 1788336313] ⟨7443055734707, 2, [(2, 1), (2081, 1), (1788336313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2081
    · exact prime_1788336313
  · decide +kernel

theorem prime_7448131939949 : Nat.Prime 7448131939949 := by
  apply nodeValid_prime [2, 7, 23, 1801, 917381] ⟨7448131939949, 2, [(2, 2), (7, 2), (23, 1), (1801, 1), (917381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_1801
    · exact prime_917381
  · decide +kernel

theorem prime_7448131940083 : Nat.Prime 7448131940083 := by
  apply nodeValid_prime [2, 3, 1241355323347] ⟨7448131940083, 5, [(2, 1), (3, 1), (1241355323347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1241355323347
  · decide +kernel

theorem prime_7448131999241 : Nat.Prime 7448131999241 := by
  apply nodeValid_prime [2, 5, 17, 10953135293] ⟨7448131999241, 3, [(2, 3), (5, 1), (17, 1), (10953135293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_10953135293
  · decide +kernel

theorem prime_7453210599097 : Nat.Prime 7453210599097 := by
  apply nodeValid_prime [2, 3, 17, 18267673037] ⟨7453210599097, 11, [(2, 3), (3, 1), (17, 1), (18267673037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_18267673037
  · decide +kernel

theorem prime_7453210608001 : Nat.Prime 7453210608001 := by
  apply nodeValid_prime [2, 3, 5, 113, 458039] ⟨7453210608001, 13, [(2, 7), (3, 2), (5, 3), (113, 1), (458039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_458039
  · decide +kernel

theorem prime_7453210608139 : Nat.Prime 7453210608139 := by
  apply nodeValid_prime [2, 3, 8941, 138933203] ⟨7453210608139, 2, [(2, 1), (3, 1), (8941, 1), (138933203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8941
    · exact prime_138933203
  · decide +kernel

theorem prime_7458291532213 : Nat.Prime 7458291532213 := by
  apply nodeValid_prime [2, 3, 29, 43, 498415633] ⟨7458291532213, 2, [(2, 2), (3, 1), (29, 1), (43, 1), (498415633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
    · exact prime_498415633
  · decide +kernel

theorem prime_7458291640963 : Nat.Prime 7458291640963 := by
  apply nodeValid_prime [2, 3, 29, 67, 97, 557, 3947] ⟨7458291640963, 2, [(2, 1), (3, 2), (29, 1), (67, 1), (97, 1), (557, 1), (3947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_67
    · exact prime_97
    · exact prime_557
    · exact prime_3947
  · decide +kernel

theorem prime_7463374814393 : Nat.Prime 7463374814393 := by
  apply nodeValid_prime [2, 7, 133274550257] ⟨7463374814393, 3, [(2, 3), (7, 1), (133274550257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_133274550257
  · decide +kernel

theorem prime_7463374855213 : Nat.Prime 7463374855213 := by
  apply nodeValid_prime [2, 3, 29, 21446479469] ⟨7463374855213, 6, [(2, 2), (3, 1), (29, 1), (21446479469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_21446479469
  · decide +kernel

theorem prime_7463374855667 : Nat.Prime 7463374855667 := by
  apply nodeValid_prime [2, 23, 162247279471] ⟨7463374855667, 2, [(2, 1), (23, 1), (162247279471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_162247279471
  · decide +kernel

theorem prime_7468460451581 : Nat.Prime 7468460451581 := by
  apply nodeValid_prime [2, 5, 29, 444022619] ⟨7468460451581, 2, [(2, 2), (5, 1), (29, 2), (444022619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_444022619
  · decide +kernel

theorem prime_7468460535083 : Nat.Prime 7468460535083 := by
  apply nodeValid_prime [2, 17, 97, 467, 49991] ⟨7468460535083, 2, [(2, 1), (17, 1), (97, 2), (467, 1), (49991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97
    · exact prime_467
    · exact prime_49991
  · decide +kernel

theorem prime_7468460536769 : Nat.Prime 7468460536769 := by
  apply nodeValid_prime [2, 7, 11, 1039, 1458629] ⟨7468460536769, 6, [(2, 6), (7, 1), (11, 1), (1039, 1), (1458629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1039
    · exact prime_1458629
  · decide +kernel

theorem prime_7473548433713 : Nat.Prime 7473548433713 := by
  apply nodeValid_prime [2, 6911, 67587437] ⟨7473548433713, 3, [(2, 4), (6911, 1), (67587437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6911
    · exact prime_67587437
  · decide +kernel

theorem prime_7473548491697 : Nat.Prime 7473548491697 := by
  apply nodeValid_prime [2, 7, 83, 803953151] ⟨7473548491697, 3, [(2, 4), (7, 1), (83, 1), (803953151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
    · exact prime_803953151
  · decide +kernel

theorem prime_7473548491999 : Nat.Prime 7473548491999 := by
  apply nodeValid_prime [2, 3, 53897, 23110589] ⟨7473548491999, 7, [(2, 1), (3, 1), (53897, 1), (23110589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53897
    · exact prime_23110589
  · decide +kernel

theorem prime_7478638756471 : Nat.Prime 7478638756471 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 208260617] ⟨7478638756471, 3, [(2, 1), (3, 3), (5, 1), (7, 1), (19, 1), (208260617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_208260617
  · decide +kernel

theorem prime_7478638861117 : Nat.Prime 7478638861117 := by
  apply nodeValid_prime [2, 3, 4057, 153615949] ⟨7478638861117, 2, [(2, 2), (3, 1), (4057, 1), (153615949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4057
    · exact prime_153615949
  · decide +kernel

theorem prime_7478638864369 : Nat.Prime 7478638864369 := by
  apply nodeValid_prime [2, 3, 7, 8501, 2618263] ⟨7478638864369, 11, [(2, 4), (3, 1), (7, 1), (8501, 1), (2618263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8501
    · exact prime_2618263
  · decide +kernel

theorem prime_7483731363469 : Nat.Prime 7483731363469 := by
  apply nodeValid_prime [2, 3, 53, 7907, 55117] ⟨7483731363469, 6, [(2, 2), (3, 4), (53, 1), (7907, 1), (55117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_7907
    · exact prime_55117
  · decide +kernel

theorem prime_7483731363551 : Nat.Prime 7483731363551 := by
  apply nodeValid_prime [2, 5, 13, 42451, 271217] ⟨7483731363551, 7, [(2, 1), (5, 2), (13, 1), (42451, 1), (271217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_42451
    · exact prime_271217
  · decide +kernel

theorem prime_7483731432941 : Nat.Prime 7483731432941 := by
  apply nodeValid_prime [2, 5, 7, 223, 271, 884537] ⟨7483731432941, 3, [(2, 2), (5, 1), (7, 1), (223, 1), (271, 1), (884537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_223
    · exact prime_271
    · exact prime_884537
  · decide +kernel

theorem prime_7488826450283 : Nat.Prime 7488826450283 := by
  apply nodeValid_prime [2, 271, 1951, 7082021] ⟨7488826450283, 2, [(2, 1), (271, 1), (1951, 1), (7082021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_1951
    · exact prime_7082021
  · decide +kernel

theorem prime_7488826522453 : Nat.Prime 7488826522453 := by
  apply nodeValid_prime [2, 3, 11, 101, 1171, 53299] ⟨7488826522453, 2, [(2, 2), (3, 3), (11, 1), (101, 1), (1171, 1), (53299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_101
    · exact prime_1171
    · exact prime_53299
  · decide +kernel

theorem prime_7488826523419 : Nat.Prime 7488826523419 := by
  apply nodeValid_prime [2, 3, 641, 22397, 86939] ⟨7488826523419, 2, [(2, 1), (3, 1), (641, 1), (22397, 1), (86939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_641
    · exact prime_22397
    · exact prime_86939
  · decide +kernel

theorem prime_7493923797937 : Nat.Prime 7493923797937 := by
  apply nodeValid_prime [2, 3, 156123412457] ⟨7493923797937, 5, [(2, 4), (3, 1), (156123412457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_156123412457
  · decide +kernel

theorem prime_7493923798411 : Nat.Prime 7493923798411 := by
  apply nodeValid_prime [2, 3, 5, 7, 61, 585005761] ⟨7493923798411, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (585005761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_585005761
  · decide +kernel

theorem prime_7493923808419 : Nat.Prime 7493923808419 := by
  apply nodeValid_prime [2, 3, 17, 73469841259] ⟨7493923808419, 2, [(2, 1), (3, 1), (17, 1), (73469841259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_73469841259
  · decide +kernel

theorem prime_7499023498751 : Nat.Prime 7499023498751 := by
  apply nodeValid_prime [2, 5, 7, 283, 3028379] ⟨7499023498751, 7, [(2, 1), (5, 4), (7, 1), (283, 1), (3028379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_283
    · exact prime_3028379
  · decide +kernel

theorem prime_7499023498777 : Nat.Prime 7499023498777 := by
  apply nodeValid_prime [2, 3, 19, 167, 98474413] ⟨7499023498777, 10, [(2, 3), (3, 1), (19, 1), (167, 1), (98474413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_167
    · exact prime_98474413
  · decide +kernel

theorem prime_7499023508597 : Nat.Prime 7499023508597 := by
  apply nodeValid_prime [2, 21617, 86725997] ⟨7499023508597, 2, [(2, 2), (21617, 1), (86725997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21617
    · exact prime_86725997
  · decide +kernel

theorem prime_7504125572347 : Nat.Prime 7504125572347 := by
  apply nodeValid_prime [2, 3, 13, 37, 2600182111] ⟨7504125572347, 2, [(2, 1), (3, 1), (13, 1), (37, 1), (2600182111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_2600182111
  · decide +kernel

theorem prime_7504125617633 : Nat.Prime 7504125617633 := by
  apply nodeValid_prime [2, 7, 1231, 1433, 2713] ⟨7504125617633, 3, [(2, 5), (7, 2), (1231, 1), (1433, 1), (2713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1231
    · exact prime_1433
    · exact prime_2713
  · decide +kernel

theorem prime_7504125618439 : Nat.Prime 7504125618439 := by
  apply nodeValid_prime [2, 3, 43, 199, 461, 105683] ⟨7504125618439, 6, [(2, 1), (3, 2), (43, 1), (199, 1), (461, 1), (105683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_199
    · exact prime_461
    · exact prime_105683
  · decide +kernel

theorem prime_7509229957739 : Nat.Prime 7509229957739 := by
  apply nodeValid_prime [2, 5227, 718311647] ⟨7509229957739, 2, [(2, 1), (5227, 1), (718311647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5227
    · exact prime_718311647
  · decide +kernel

theorem prime_7509229959149 : Nat.Prime 7509229959149 := by
  apply nodeValid_prime [2, 2729, 687910403] ⟨7509229959149, 2, [(2, 2), (2729, 1), (687910403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2729
    · exact prime_687910403
  · decide +kernel

theorem prime_7509229984469 : Nat.Prime 7509229984469 := by
  apply nodeValid_prime [2, 89, 21093342653] ⟨7509229984469, 2, [(2, 2), (89, 1), (21093342653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_21093342653
  · decide +kernel

theorem prime_7514336387603 : Nat.Prime 7514336387603 := by
  apply nodeValid_prime [2, 11, 17, 43, 467251361] ⟨7514336387603, 2, [(2, 1), (11, 1), (17, 1), (43, 1), (467251361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_43
    · exact prime_467251361
  · decide +kernel

theorem prime_7514336388953 : Nat.Prime 7514336388953 := by
  apply nodeValid_prime [2, 171491, 5477209] ⟨7514336388953, 3, [(2, 3), (171491, 1), (5477209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_171491
    · exact prime_5477209
  · decide +kernel

theorem prime_7514336737949 : Nat.Prime 7514336737949 := by
  apply nodeValid_prime [2, 139, 13514994133] ⟨7514336737949, 2, [(2, 2), (139, 1), (13514994133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_13514994133
  · decide +kernel

theorem prime_7519445827273 : Nat.Prime 7519445827273 := by
  apply nodeValid_prime [2, 3, 1399, 1913, 39023] ⟨7519445827273, 5, [(2, 3), (3, 2), (1399, 1), (1913, 1), (39023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1399
    · exact prime_1913
    · exact prime_39023
  · decide +kernel

theorem prime_7519445843837 : Nat.Prime 7519445843837 := by
  apply nodeValid_prime [2, 31, 133087, 455647] ⟨7519445843837, 2, [(2, 2), (31, 1), (133087, 1), (455647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_133087
    · exact prime_455647
  · decide +kernel

theorem prime_7519445844373 : Nat.Prime 7519445844373 := by
  apply nodeValid_prime [2, 3, 7, 11, 82201297] ⟨7519445844373, 2, [(2, 2), (3, 3), (7, 1), (11, 2), (82201297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_82201297
  · decide +kernel

theorem prime_7524557261233 : Nat.Prime 7524557261233 := by
  apply nodeValid_prime [2, 3, 11, 14251055419] ⟨7524557261233, 15, [(2, 4), (3, 1), (11, 1), (14251055419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_14251055419
  · decide +kernel

theorem prime_7524557299151 : Nat.Prime 7524557299151 := by
  apply nodeValid_prime [2, 5, 150491145983] ⟨7524557299151, 19, [(2, 1), (5, 2), (150491145983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_150491145983
  · decide +kernel

theorem prime_7524557299199 : Nat.Prime 7524557299199 := by
  apply nodeValid_prime [2, 13159, 285909161] ⟨7524557299199, 13, [(2, 1), (13159, 1), (285909161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13159
    · exact prime_285909161
  · decide +kernel

theorem prime_7529670992561 : Nat.Prime 7529670992561 := by
  apply nodeValid_prime [2, 5, 2179, 43194533] ⟨7529670992561, 3, [(2, 4), (5, 1), (2179, 1), (43194533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2179
    · exact prime_43194533
  · decide +kernel

theorem prime_7529670993277 : Nat.Prime 7529670993277 := by
  apply nodeValid_prime [2, 3, 209157527591] ⟨7529670993277, 5, [(2, 2), (3, 2), (209157527591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_209157527591
  · decide +kernel

theorem prime_7529671044041 : Nat.Prime 7529671044041 := by
  apply nodeValid_prime [2, 5, 17, 1231, 8995163] ⟨7529671044041, 3, [(2, 3), (5, 1), (17, 1), (1231, 1), (8995163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1231
    · exact prime_8995163
  · decide +kernel

end Sude.Lucas.Generated
