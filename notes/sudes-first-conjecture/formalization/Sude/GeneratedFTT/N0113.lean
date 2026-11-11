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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0103

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10243 : Nat.Prime 10243 := by
  apply nodeValid_prime [2, 3, 569] ⟨10243, 7, [(2, 1), (3, 2), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
  · decide +kernel

theorem prime_17471 : Nat.Prime 17471 := by
  apply nodeValid_prime [2, 5, 1747] ⟨17471, 11, [(2, 1), (5, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1747
  · decide +kernel

theorem prime_17659 : Nat.Prime 17659 := by
  apply nodeValid_prime [2, 3, 109] ⟨17659, 3, [(2, 1), (3, 4), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_19009 : Nat.Prime 19009 := by
  apply nodeValid_prime [2, 3, 11] ⟨19009, 23, [(2, 6), (3, 3), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_19597 : Nat.Prime 19597 := by
  apply nodeValid_prime [2, 3, 23, 71] ⟨19597, 2, [(2, 2), (3, 1), (23, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_71
  · decide +kernel

theorem prime_24631 : Nat.Prime 24631 := by
  apply nodeValid_prime [2, 3, 5, 821] ⟨24631, 3, [(2, 1), (3, 1), (5, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_821
  · decide +kernel

theorem prime_30091 : Nat.Prime 30091 := by
  apply nodeValid_prime [2, 3, 5, 17, 59] ⟨30091, 21, [(2, 1), (3, 1), (5, 1), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_32429 : Nat.Prime 32429 := by
  apply nodeValid_prime [2, 11, 67] ⟨32429, 3, [(2, 2), (11, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_33797 : Nat.Prime 33797 := by
  apply nodeValid_prime [2, 7, 17, 71] ⟨33797, 3, [(2, 2), (7, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_35603 : Nat.Prime 35603 := by
  apply nodeValid_prime [2, 7, 2543] ⟨35603, 2, [(2, 1), (7, 1), (2543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2543
  · decide +kernel

theorem prime_36251 : Nat.Prime 36251 := by
  apply nodeValid_prime [2, 5, 29] ⟨36251, 2, [(2, 1), (5, 4), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_36497 : Nat.Prime 36497 := by
  apply nodeValid_prime [2, 2281] ⟨36497, 3, [(2, 4), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2281
  · decide +kernel

theorem prime_37489 : Nat.Prime 37489 := by
  apply nodeValid_prime [2, 3, 11, 71] ⟨37489, 19, [(2, 4), (3, 1), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_49169 : Nat.Prime 49169 := by
  apply nodeValid_prime [2, 7, 439] ⟨49169, 3, [(2, 4), (7, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_439
  · decide +kernel

theorem prime_50651 : Nat.Prime 50651 := by
  apply nodeValid_prime [2, 5, 1013] ⟨50651, 2, [(2, 1), (5, 2), (1013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1013
  · decide +kernel

theorem prime_72503 : Nat.Prime 72503 := by
  apply nodeValid_prime [2, 36251] ⟨72503, 5, [(2, 1), (36251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36251
  · decide +kernel

theorem prime_75583 : Nat.Prime 75583 := by
  apply nodeValid_prime [2, 3, 13, 17, 19] ⟨75583, 5, [(2, 1), (3, 2), (13, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_86477 : Nat.Prime 86477 := by
  apply nodeValid_prime [2, 13, 1663] ⟨86477, 2, [(2, 2), (13, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1663
  · decide +kernel

theorem prime_94837 : Nat.Prime 94837 := by
  apply nodeValid_prime [2, 3, 7, 1129] ⟨94837, 2, [(2, 2), (3, 1), (7, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1129
  · decide +kernel

theorem prime_100907 : Nat.Prime 100907 := by
  apply nodeValid_prime [2, 13, 3881] ⟨100907, 2, [(2, 1), (13, 1), (3881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3881
  · decide +kernel

theorem prime_119173 : Nat.Prime 119173 := by
  apply nodeValid_prime [2, 3, 9931] ⟨119173, 2, [(2, 2), (3, 1), (9931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9931
  · decide +kernel

theorem prime_120397 : Nat.Prime 120397 := by
  apply nodeValid_prime [2, 3, 79, 127] ⟨120397, 2, [(2, 2), (3, 1), (79, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_127
  · decide +kernel

theorem prime_145007 : Nat.Prime 145007 := by
  apply nodeValid_prime [2, 72503] ⟨145007, 5, [(2, 1), (72503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_72503
  · decide +kernel

theorem prime_175691 : Nat.Prime 175691 := by
  apply nodeValid_prime [2, 5, 17569] ⟨175691, 2, [(2, 1), (5, 1), (17569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17569
  · decide +kernel

theorem prime_181081 : Nat.Prime 181081 := by
  apply nodeValid_prime [2, 3, 5, 503] ⟨181081, 11, [(2, 3), (3, 2), (5, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_503
  · decide +kernel

theorem prime_196039 : Nat.Prime 196039 := by
  apply nodeValid_prime [2, 3, 10891] ⟨196039, 3, [(2, 1), (3, 2), (10891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10891
  · decide +kernel

theorem prime_209659 : Nat.Prime 209659 := by
  apply nodeValid_prime [2, 3, 83, 421] ⟨209659, 2, [(2, 1), (3, 1), (83, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_421
  · decide +kernel

theorem prime_210601 : Nat.Prime 210601 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨210601, 7, [(2, 3), (3, 4), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_219437 : Nat.Prime 219437 := by
  apply nodeValid_prime [2, 7, 17, 461] ⟨219437, 2, [(2, 2), (7, 1), (17, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_461
  · decide +kernel

theorem prime_241013 : Nat.Prime 241013 := by
  apply nodeValid_prime [2, 89, 677] ⟨241013, 2, [(2, 2), (89, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_677
  · decide +kernel

theorem prime_252233 : Nat.Prime 252233 := by
  apply nodeValid_prime [2, 41, 769] ⟨252233, 3, [(2, 3), (41, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_769
  · decide +kernel

theorem prime_264697 : Nat.Prime 264697 := by
  apply nodeValid_prime [2, 3, 41, 269] ⟨264697, 7, [(2, 3), (3, 1), (41, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_269
  · decide +kernel

theorem prime_303907 : Nat.Prime 303907 := by
  apply nodeValid_prime [2, 3, 50651] ⟨303907, 2, [(2, 1), (3, 1), (50651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50651
  · decide +kernel

theorem prime_304259 : Nat.Prime 304259 := by
  apply nodeValid_prime [2, 149, 1021] ⟨304259, 2, [(2, 1), (149, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_1021
  · decide +kernel

theorem prime_351383 : Nat.Prime 351383 := by
  apply nodeValid_prime [2, 175691] ⟨351383, 5, [(2, 1), (175691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_175691
  · decide +kernel

theorem prime_366133 : Nat.Prime 366133 := by
  apply nodeValid_prime [2, 3, 13, 2347] ⟨366133, 7, [(2, 2), (3, 1), (13, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2347
  · decide +kernel

theorem prime_394363 : Nat.Prime 394363 := by
  apply nodeValid_prime [2, 3, 67, 109] ⟨394363, 2, [(2, 1), (3, 3), (67, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_109
  · decide +kernel

theorem prime_418699 : Nat.Prime 418699 := by
  apply nodeValid_prime [2, 3, 7, 3323] ⟨418699, 3, [(2, 1), (3, 2), (7, 1), (3323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3323
  · decide +kernel

theorem prime_473159 : Nat.Prime 473159 := by
  apply nodeValid_prime [2, 7, 33797] ⟨473159, 7, [(2, 1), (7, 1), (33797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_33797
  · decide +kernel

theorem prime_481589 : Nat.Prime 481589 := by
  apply nodeValid_prime [2, 120397] ⟨481589, 2, [(2, 2), (120397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_120397
  · decide +kernel

theorem prime_495277 : Nat.Prime 495277 := by
  apply nodeValid_prime [2, 3, 149, 277] ⟨495277, 5, [(2, 2), (3, 1), (149, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_277
  · decide +kernel

theorem prime_542557 : Nat.Prime 542557 := by
  apply nodeValid_prime [2, 3, 7, 2153] ⟨542557, 2, [(2, 2), (3, 2), (7, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2153
  · decide +kernel

theorem prime_606569 : Nat.Prime 606569 := by
  apply nodeValid_prime [2, 75821] ⟨606569, 3, [(2, 3), (75821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_75821
  · decide +kernel

theorem prime_608519 : Nat.Prime 608519 := by
  apply nodeValid_prime [2, 304259] ⟨608519, 7, [(2, 1), (304259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_304259
  · decide +kernel

theorem prime_623107 : Nat.Prime 623107 := by
  apply nodeValid_prime [2, 3, 11, 1049] ⟨623107, 3, [(2, 1), (3, 3), (11, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1049
  · decide +kernel

theorem prime_702199 : Nat.Prime 702199 := by
  apply nodeValid_prime [2, 3, 7, 5573] ⟨702199, 6, [(2, 1), (3, 2), (7, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5573
  · decide +kernel

theorem prime_778597 : Nat.Prime 778597 := by
  apply nodeValid_prime [2, 3, 7, 13, 23, 31] ⟨778597, 2, [(2, 2), (3, 1), (7, 1), (13, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_946391 : Nat.Prime 946391 := by
  apply nodeValid_prime [2, 5, 17, 19, 293] ⟨946391, 19, [(2, 1), (5, 1), (17, 1), (19, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_293
  · decide +kernel

theorem prime_1039111 : Nat.Prime 1039111 := by
  apply nodeValid_prime [2, 3, 5, 19, 1823] ⟨1039111, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1823
  · decide +kernel

theorem prime_1054927 : Nat.Prime 1054927 := by
  apply nodeValid_prime [2, 3, 103, 569] ⟨1054927, 5, [(2, 1), (3, 2), (103, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_569
  · decide +kernel

theorem prime_1203641 : Nat.Prime 1203641 := by
  apply nodeValid_prime [2, 5, 30091] ⟨1203641, 6, [(2, 3), (5, 1), (30091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30091
  · decide +kernel

theorem prime_1531111 : Nat.Prime 1531111 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 317] ⟨1531111, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_317
  · decide +kernel

theorem prime_1563109 : Nat.Prime 1563109 := by
  apply nodeValid_prime [2, 3, 130259] ⟨1563109, 2, [(2, 2), (3, 1), (130259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130259
  · decide +kernel

theorem prime_1574747 : Nat.Prime 1574747 := by
  apply nodeValid_prime [2, 43, 18311] ⟨1574747, 2, [(2, 1), (43, 1), (18311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_18311
  · decide +kernel

theorem prime_1804093 : Nat.Prime 1804093 := by
  apply nodeValid_prime [2, 3, 149, 1009] ⟨1804093, 2, [(2, 2), (3, 1), (149, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_1009
  · decide +kernel

theorem prime_1922563 : Nat.Prime 1922563 := by
  apply nodeValid_prime [2, 3, 35603] ⟨1922563, 2, [(2, 1), (3, 3), (35603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35603
  · decide +kernel

theorem prime_2068061 : Nat.Prime 2068061 := by
  apply nodeValid_prime [2, 5, 53, 1951] ⟨2068061, 2, [(2, 2), (5, 1), (53, 1), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_1951
  · decide +kernel

theorem prime_2864569 : Nat.Prime 2864569 := by
  apply nodeValid_prime [2, 3, 7, 17, 59] ⟨2864569, 13, [(2, 3), (3, 1), (7, 1), (17, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_2965483 : Nat.Prime 2965483 := by
  apply nodeValid_prime [2, 3, 13, 19, 23, 29] ⟨2965483, 11, [(2, 1), (3, 2), (13, 1), (19, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_3114389 : Nat.Prime 3114389 := by
  apply nodeValid_prime [2, 778597] ⟨3114389, 2, [(2, 2), (778597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_778597
  · decide +kernel

theorem prime_4280629 : Nat.Prime 4280629 := by
  apply nodeValid_prime [2, 3, 11, 32429] ⟨4280629, 6, [(2, 2), (3, 1), (11, 1), (32429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_32429
  · decide +kernel

theorem prime_5058491 : Nat.Prime 5058491 := by
  apply nodeValid_prime [2, 5, 353, 1433] ⟨5058491, 2, [(2, 1), (5, 1), (353, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_353
    · exact prime_1433
  · decide +kernel

theorem prime_5779069 : Nat.Prime 5779069 := by
  apply nodeValid_prime [2, 3, 481589] ⟨5779069, 6, [(2, 2), (3, 1), (481589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_481589
  · decide +kernel

theorem prime_6228779 : Nat.Prime 6228779 := by
  apply nodeValid_prime [2, 3114389] ⟨6228779, 2, [(2, 1), (3114389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3114389
  · decide +kernel

theorem prime_9211379 : Nat.Prime 9211379 := by
  apply nodeValid_prime [2, 11, 418699] ⟨9211379, 2, [(2, 1), (11, 1), (418699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_418699
  · decide +kernel

theorem prime_9629129 : Nat.Prime 9629129 := by
  apply nodeValid_prime [2, 1203641] ⟨9629129, 3, [(2, 3), (1203641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1203641
  · decide +kernel

theorem prime_10549271 : Nat.Prime 10549271 := by
  apply nodeValid_prime [2, 5, 1054927] ⟨10549271, 13, [(2, 1), (5, 1), (1054927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1054927
  · decide +kernel

theorem prime_12790039 : Nat.Prime 12790039 := by
  apply nodeValid_prime [2, 3, 73, 29201] ⟨12790039, 11, [(2, 1), (3, 1), (73, 1), (29201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_29201
  · decide +kernel

theorem prime_15216653 : Nat.Prime 15216653 := by
  apply nodeValid_prime [2, 11, 239, 1447] ⟨15216653, 2, [(2, 2), (11, 1), (239, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_1447
  · decide +kernel

theorem prime_16316917 : Nat.Prime 16316917 := by
  apply nodeValid_prime [2, 3, 7, 11, 17659] ⟨16316917, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (17659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17659
  · decide +kernel

theorem prime_16451251 : Nat.Prime 16451251 := by
  apply nodeValid_prime [2, 3, 5, 41, 107] ⟨16451251, 13, [(2, 1), (3, 1), (5, 4), (41, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_107
  · decide +kernel

theorem prime_16981441 : Nat.Prime 16981441 := by
  apply nodeValid_prime [2, 3, 5, 7, 19] ⟨16981441, 17, [(2, 6), (3, 1), (5, 1), (7, 2), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_19258259 : Nat.Prime 19258259 := by
  apply nodeValid_prime [2, 9629129] ⟨19258259, 2, [(2, 1), (9629129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9629129
  · decide +kernel

theorem prime_19591541 : Nat.Prime 19591541 := by
  apply nodeValid_prime [2, 5, 59, 16603] ⟨19591541, 2, [(2, 2), (5, 1), (59, 1), (16603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_16603
  · decide +kernel

theorem prime_24451331 : Nat.Prime 24451331 := by
  apply nodeValid_prime [2, 5, 823, 2971] ⟨24451331, 2, [(2, 1), (5, 1), (823, 1), (2971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_823
    · exact prime_2971
  · decide +kernel

theorem prime_27140033 : Nat.Prime 27140033 := by
  apply nodeValid_prime [2, 41, 10343] ⟨27140033, 3, [(2, 6), (41, 1), (10343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_10343
  · decide +kernel

theorem prime_29654831 : Nat.Prime 29654831 := by
  apply nodeValid_prime [2, 5, 2965483] ⟨29654831, 13, [(2, 1), (5, 1), (2965483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2965483
  · decide +kernel

theorem prime_36019523 : Nat.Prime 36019523 := by
  apply nodeValid_prime [2, 7, 11, 1933] ⟨36019523, 2, [(2, 1), (7, 1), (11, 3), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1933
  · decide +kernel

theorem prime_38223467 : Nat.Prime 38223467 := by
  apply nodeValid_prime [2, 109, 271, 647] ⟨38223467, 2, [(2, 1), (109, 1), (271, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_271
    · exact prime_647
  · decide +kernel

theorem prime_49012367 : Nat.Prime 49012367 := by
  apply nodeValid_prime [2, 13, 145007] ⟨49012367, 10, [(2, 1), (13, 2), (145007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_145007
  · decide +kernel

theorem prime_49830233 : Nat.Prime 49830233 := by
  apply nodeValid_prime [2, 6228779] ⟨49830233, 3, [(2, 3), (6228779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6228779
  · decide +kernel

theorem prime_53633369 : Nat.Prime 53633369 := by
  apply nodeValid_prime [2, 17, 394363] ⟨53633369, 3, [(2, 3), (17, 1), (394363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_394363
  · decide +kernel

theorem prime_70700033 : Nat.Prime 70700033 := by
  apply nodeValid_prime [2, 13, 47, 113] ⟨70700033, 3, [(2, 10), (13, 1), (47, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_113
  · decide +kernel

theorem prime_82947187 : Nat.Prime 82947187 := by
  apply nodeValid_prime [2, 3, 7, 219437] ⟨82947187, 3, [(2, 1), (3, 3), (7, 1), (219437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_219437
  · decide +kernel

theorem prime_91866661 : Nat.Prime 91866661 := by
  apply nodeValid_prime [2, 3, 5, 1531111] ⟨91866661, 6, [(2, 2), (3, 1), (5, 1), (1531111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1531111
  · decide +kernel

theorem prime_107652229 : Nat.Prime 107652229 := by
  apply nodeValid_prime [2, 3, 17, 523, 1009] ⟨107652229, 2, [(2, 2), (3, 1), (17, 1), (523, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_523
    · exact prime_1009
  · decide +kernel

theorem prime_114582761 : Nat.Prime 114582761 := by
  apply nodeValid_prime [2, 5, 2864569] ⟨114582761, 3, [(2, 3), (5, 1), (2864569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2864569
  · decide +kernel

theorem prime_115394659 : Nat.Prime 115394659 := by
  apply nodeValid_prime [2, 3, 4021, 4783] ⟨115394659, 2, [(2, 1), (3, 1), (4021, 1), (4783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4021
    · exact prime_4783
  · decide +kernel

theorem prime_240495067 : Nat.Prime 240495067 := by
  apply nodeValid_prime [2, 3, 7, 1237, 1543] ⟨240495067, 3, [(2, 1), (3, 2), (7, 1), (1237, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1237
    · exact prime_1543
  · decide +kernel

theorem prime_241513429 : Nat.Prime 241513429 := by
  apply nodeValid_prime [2, 3, 13, 79, 19597] ⟨241513429, 2, [(2, 2), (3, 1), (13, 1), (79, 1), (19597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_79
    · exact prime_19597
  · decide +kernel

theorem prime_284786849 : Nat.Prime 284786849 := by
  apply nodeValid_prime [2, 181, 49169] ⟨284786849, 3, [(2, 5), (181, 1), (49169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_49169
  · decide +kernel

theorem prime_353908297 : Nat.Prime 353908297 := by
  apply nodeValid_prime [2, 3, 7, 702199] ⟨353908297, 5, [(2, 3), (3, 2), (7, 1), (702199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_702199
  · decide +kernel

theorem prime_405712687 : Nat.Prime 405712687 := by
  apply nodeValid_prime [2, 3, 23, 31, 94837] ⟨405712687, 3, [(2, 1), (3, 1), (23, 1), (31, 1), (94837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_31
    · exact prime_94837
  · decide +kernel

theorem prime_459804473 : Nat.Prime 459804473 := by
  apply nodeValid_prime [2, 881, 65239] ⟨459804473, 3, [(2, 3), (881, 1), (65239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_881
    · exact prime_65239
  · decide +kernel

theorem prime_473883659 : Nat.Prime 473883659 := by
  apply nodeValid_prime [2, 41, 5779069] ⟨473883659, 2, [(2, 1), (41, 1), (5779069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_5779069
  · decide +kernel

theorem prime_507741011 : Nat.Prime 507741011 := by
  apply nodeValid_prime [2, 5, 7, 37, 196039] ⟨507741011, 2, [(2, 1), (5, 1), (7, 1), (37, 1), (196039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_196039
  · decide +kernel

theorem prime_672850099 : Nat.Prime 672850099 := by
  apply nodeValid_prime [2, 3, 41, 303907] ⟨672850099, 2, [(2, 1), (3, 3), (41, 1), (303907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_303907
  · decide +kernel

theorem prime_1100330237 : Nat.Prime 1100330237 := by
  apply nodeValid_prime [2, 17, 881, 18367] ⟨1100330237, 2, [(2, 2), (17, 1), (881, 1), (18367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_881
    · exact prime_18367
  · decide +kernel

theorem prime_1120303829 : Nat.Prime 1120303829 := by
  apply nodeValid_prime [2, 7, 97, 397, 1039] ⟨1120303829, 2, [(2, 2), (7, 1), (97, 1), (397, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_97
    · exact prime_397
    · exact prime_1039
  · decide +kernel

theorem prime_1388014289 : Nat.Prime 1388014289 := by
  apply nodeValid_prime [2, 3347, 25919] ⟨1388014289, 3, [(2, 4), (3347, 1), (25919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3347
    · exact prime_25919
  · decide +kernel

theorem prime_3791069273 : Nat.Prime 3791069273 := by
  apply nodeValid_prime [2, 473883659] ⟨3791069273, 3, [(2, 3), (473883659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_473883659
  · decide +kernel

theorem prime_3918288029 : Nat.Prime 3918288029 := by
  apply nodeValid_prime [2, 31, 1543, 20479] ⟨3918288029, 2, [(2, 2), (31, 1), (1543, 1), (20479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1543
    · exact prime_20479
  · decide +kernel

theorem prime_4076588273 : Nat.Prime 4076588273 := by
  apply nodeValid_prime [2, 163, 1563109] ⟨4076588273, 3, [(2, 4), (163, 1), (1563109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_1563109
  · decide +kernel

theorem prime_4561449419 : Nat.Prime 4561449419 := by
  apply nodeValid_prime [2, 17, 59, 181, 739] ⟨4561449419, 2, [(2, 1), (17, 2), (59, 1), (181, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
    · exact prime_181
    · exact prime_739
  · decide +kernel

theorem prime_7358820143 : Nat.Prime 7358820143 := by
  apply nodeValid_prime [2, 17471, 210601] ⟨7358820143, 5, [(2, 1), (17471, 1), (210601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17471
    · exact prime_210601
  · decide +kernel

theorem prime_7668556439 : Nat.Prime 7668556439 := by
  apply nodeValid_prime [2, 6301, 608519] ⟨7668556439, 11, [(2, 1), (6301, 1), (608519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6301
    · exact prime_608519
  · decide +kernel

theorem prime_16174081111 : Nat.Prime 16174081111 := by
  apply nodeValid_prime [2, 3, 5, 11, 49012367] ⟨16174081111, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (49012367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_49012367
  · decide +kernel

theorem prime_85399148279 : Nat.Prime 85399148279 := by
  apply nodeValid_prime [2, 487, 1511, 58027] ⟨85399148279, 7, [(2, 1), (487, 1), (1511, 1), (58027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_1511
    · exact prime_58027
  · decide +kernel

theorem prime_101748625273 : Nat.Prime 101748625273 := by
  apply nodeValid_prime [2, 3, 7, 2671, 75583] ⟨101748625273, 5, [(2, 3), (3, 2), (7, 1), (2671, 1), (75583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2671
    · exact prime_75583
  · decide +kernel

theorem prime_117644854913 : Nat.Prime 117644854913 := by
  apply nodeValid_prime [2, 13, 70700033] ⟨117644854913, 3, [(2, 7), (13, 1), (70700033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_70700033
  · decide +kernel

theorem prime_163159536671 : Nat.Prime 163159536671 := by
  apply nodeValid_prime [2, 5, 13, 797, 1574747] ⟨163159536671, 17, [(2, 1), (5, 1), (13, 1), (797, 1), (1574747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_797
    · exact prime_1574747
  · decide +kernel

theorem prime_176611683433 : Nat.Prime 176611683433 := by
  apply nodeValid_prime [2, 3, 7358820143] ⟨176611683433, 10, [(2, 3), (3, 1), (7358820143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7358820143
  · decide +kernel

theorem prime_194088973333 : Nat.Prime 194088973333 := by
  apply nodeValid_prime [2, 3, 16174081111] ⟨194088973333, 5, [(2, 2), (3, 1), (16174081111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16174081111
  · decide +kernel

theorem prime_235289709827 : Nat.Prime 235289709827 := by
  apply nodeValid_prime [2, 117644854913] ⟨235289709827, 2, [(2, 1), (117644854913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117644854913
  · decide +kernel

theorem prime_304748186819 : Nat.Prime 304748186819 := by
  apply nodeValid_prime [2, 23, 241, 389, 70667] ⟨304748186819, 2, [(2, 1), (23, 1), (241, 1), (389, 1), (70667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_241
    · exact prime_389
    · exact prime_70667
  · decide +kernel

theorem prime_306742257869 : Nat.Prime 306742257869 := by
  apply nodeValid_prime [2, 2129, 36019523] ⟨306742257869, 2, [(2, 2), (2129, 1), (36019523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2129
    · exact prime_36019523
  · decide +kernel

theorem prime_353223368471 : Nat.Prime 353223368471 := by
  apply nodeValid_prime [2, 5, 7, 2797, 1804093] ⟨353223368471, 14, [(2, 1), (5, 1), (7, 1), (2797, 1), (1804093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2797
    · exact prime_1804093
  · decide +kernel

theorem prime_354380172889 : Nat.Prime 354380172889 := by
  apply nodeValid_prime [2, 3, 7, 229, 9211379] ⟨354380172889, 11, [(2, 3), (3, 1), (7, 1), (229, 1), (9211379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_229
    · exact prime_9211379
  · decide +kernel

theorem prime_356701473221 : Nat.Prime 356701473221 := by
  apply nodeValid_prime [2, 5, 109, 1373, 119173] ⟨356701473221, 2, [(2, 2), (5, 1), (109, 1), (1373, 1), (119173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_1373
    · exact prime_119173
  · decide +kernel

theorem prime_423521477191 : Nat.Prime 423521477191 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 5717, 6917] ⟨423521477191, 6, [(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (5717, 1), (6917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_5717
    · exact prime_6917
  · decide +kernel

theorem prime_2138464506599 : Nat.Prime 2138464506599 := by
  apply nodeValid_prime [2, 7, 6247, 24451331] ⟨2138464506599, 7, [(2, 1), (7, 1), (6247, 1), (24451331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6247
    · exact prime_24451331
  · decide +kernel

theorem prime_2148944934113 : Nat.Prime 2148944934113 := by
  apply nodeValid_prime [2, 17, 43, 91866661] ⟨2148944934113, 3, [(2, 5), (17, 1), (43, 1), (91866661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_43
    · exact prime_91866661
  · decide +kernel

theorem prime_4231751071321 : Nat.Prime 4231751071321 := by
  apply nodeValid_prime [2, 3, 5, 3918288029] ⟨4231751071321, 23, [(2, 3), (3, 3), (5, 1), (3918288029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3918288029
  · decide +kernel

theorem prime_4231751198933 : Nat.Prime 4231751198933 := by
  apply nodeValid_prime [2, 53, 83, 240495067] ⟨4231751198933, 2, [(2, 2), (53, 1), (83, 1), (240495067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_83
    · exact prime_240495067
  · decide +kernel

theorem prime_4231751199301 : Nat.Prime 4231751199301 := by
  apply nodeValid_prime [2, 3, 5, 103, 15216653] ⟨4231751199301, 6, [(2, 2), (3, 3), (5, 2), (103, 1), (15216653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_15216653
  · decide +kernel

theorem prime_4235214771911 : Nat.Prime 4235214771911 := by
  apply nodeValid_prime [2, 5, 423521477191] ⟨4235214771911, 7, [(2, 1), (5, 1), (423521477191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_423521477191
  · decide +kernel

theorem prime_4235214774619 : Nat.Prime 4235214774619 := by
  apply nodeValid_prime [2, 3, 2039, 115394659] ⟨4235214774619, 2, [(2, 1), (3, 2), (2039, 1), (115394659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2039
    · exact prime_115394659
  · decide +kernel

theorem prime_4235214776887 : Nat.Prime 4235214776887 := by
  apply nodeValid_prime [2, 3, 235289709827] ⟨4235214776887, 3, [(2, 1), (3, 2), (235289709827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_235289709827
  · decide +kernel

theorem prime_4238680402393 : Nat.Prime 4238680402393 := by
  apply nodeValid_prime [2, 3, 176611683433] ⟨4238680402393, 5, [(2, 3), (3, 1), (176611683433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_176611683433
  · decide +kernel

theorem prime_4238680421551 : Nat.Prime 4238680421551 := by
  apply nodeValid_prime [2, 3, 5, 137, 587, 351383] ⟨4238680421551, 6, [(2, 1), (3, 1), (5, 2), (137, 1), (587, 1), (351383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_587
    · exact prime_351383
  · decide +kernel

theorem prime_4238680421653 : Nat.Prime 4238680421653 := by
  apply nodeValid_prime [2, 3, 353223368471] ⟨4238680421653, 2, [(2, 2), (3, 1), (353223368471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353223368471
  · decide +kernel

theorem prime_4242147953447 : Nat.Prime 4242147953447 := by
  apply nodeValid_prime [2, 13, 163159536671] ⟨4242147953447, 5, [(2, 1), (13, 1), (163159536671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_163159536671
  · decide +kernel

theorem prime_4242147956041 : Nat.Prime 4242147956041 := by
  apply nodeValid_prime [2, 3, 5, 23, 7331, 209659] ⟨4242147956041, 11, [(2, 3), (3, 1), (5, 1), (23, 1), (7331, 1), (209659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_7331
    · exact prime_209659
  · decide +kernel

theorem prime_4242147959671 : Nat.Prime 4242147959671 := by
  apply nodeValid_prime [2, 3, 5, 31, 4561449419] ⟨4242147959671, 3, [(2, 1), (3, 1), (5, 1), (31, 1), (4561449419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_4561449419
  · decide +kernel

theorem prime_4245617409577 : Nat.Prime 4245617409577 := by
  apply nodeValid_prime [2, 3, 41, 409, 10549271] ⟨4245617409577, 5, [(2, 3), (3, 1), (41, 1), (409, 1), (10549271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_409
    · exact prime_10549271
  · decide +kernel

theorem prime_4245617489923 : Nat.Prime 4245617489923 := by
  apply nodeValid_prime [2, 3, 113, 5701, 366133] ⟨4245617489923, 3, [(2, 1), (3, 2), (113, 1), (5701, 1), (366133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_5701
    · exact prime_366133
  · decide +kernel

theorem prime_4245617490041 : Nat.Prime 4245617490041 := by
  apply nodeValid_prime [2, 5, 1979, 53633369] ⟨4245617490041, 3, [(2, 3), (5, 1), (1979, 1), (53633369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1979
    · exact prime_53633369
  · decide +kernel

theorem prime_4249088788283 : Nat.Prime 4249088788283 := by
  apply nodeValid_prime [2, 13, 67, 149, 1621, 10099] ⟨4249088788283, 2, [(2, 1), (13, 1), (67, 1), (149, 1), (1621, 1), (10099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_149
    · exact prime_1621
    · exact prime_10099
  · decide +kernel

theorem prime_4249088834539 : Nat.Prime 4249088834539 := by
  apply nodeValid_prime [2, 3, 23, 433, 2887, 24631] ⟨4249088834539, 2, [(2, 1), (3, 1), (23, 1), (433, 1), (2887, 1), (24631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_433
    · exact prime_2887
    · exact prime_24631
  · decide +kernel

theorem prime_4249088835137 : Nat.Prime 4249088835137 := by
  apply nodeValid_prime [2, 23, 569, 647, 7841] ⟨4249088835137, 3, [(2, 6), (23, 1), (569, 1), (647, 1), (7841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_569
    · exact prime_647
    · exact prime_7841
  · decide +kernel

theorem prime_4252562074669 : Nat.Prime 4252562074669 := by
  apply nodeValid_prime [2, 3, 354380172889] ⟨4252562074669, 2, [(2, 2), (3, 1), (354380172889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_354380172889
  · decide +kernel

theorem prime_4252562075063 : Nat.Prime 4252562075063 := by
  apply nodeValid_prime [2, 7, 10243, 29654831] ⟨4252562075063, 5, [(2, 1), (7, 1), (10243, 1), (29654831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10243
    · exact prime_29654831
  · decide +kernel

theorem prime_4252562096753 : Nat.Prime 4252562096753 := by
  apply nodeValid_prime [2, 751, 353908297] ⟨4252562096753, 3, [(2, 4), (751, 1), (353908297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_751
    · exact prime_353908297
  · decide +kernel

theorem prime_4256037321071 : Nat.Prime 4256037321071 := by
  apply nodeValid_prime [2, 5, 103, 37489, 110221] ⟨4256037321071, 14, [(2, 1), (5, 1), (103, 1), (37489, 1), (110221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_37489
    · exact prime_110221
  · decide +kernel

theorem prime_4256037341207 : Nat.Prime 4256037341207 := by
  apply nodeValid_prime [2, 7, 17, 1087, 16451251] ⟨4256037341207, 7, [(2, 1), (7, 1), (17, 1), (1087, 1), (16451251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1087
    · exact prime_16451251
  · decide +kernel

theorem prime_4259514462293 : Nat.Prime 4259514462293 := by
  apply nodeValid_prime [2, 31, 409, 599, 4523] ⟨4259514462293, 2, [(2, 2), (31, 2), (409, 1), (599, 1), (4523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_409
    · exact prime_599
    · exact prime_4523
  · decide +kernel

theorem prime_4259514477863 : Nat.Prime 4259514477863 := by
  apply nodeValid_prime [2, 7, 5843, 6317, 8243] ⟨4259514477863, 5, [(2, 1), (7, 1), (5843, 1), (6317, 1), (8243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5843
    · exact prime_6317
    · exact prime_8243
  · decide +kernel

theorem prime_4259514478057 : Nat.Prime 4259514478057 := by
  apply nodeValid_prime [2, 3, 9059, 19591541] ⟨4259514478057, 5, [(2, 3), (3, 1), (9059, 1), (19591541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9059
    · exact prime_19591541
  · decide +kernel

theorem prime_4262993528357 : Nat.Prime 4262993528357 := by
  apply nodeValid_prime [2, 2099, 507741011] ⟨4262993528357, 2, [(2, 2), (2099, 1), (507741011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2099
    · exact prime_507741011
  · decide +kernel

theorem prime_4262993543443 : Nat.Prime 4262993543443 := by
  apply nodeValid_prime [2, 3, 47, 557, 27140033] ⟨4262993543443, 2, [(2, 1), (3, 1), (47, 1), (557, 1), (27140033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_557
    · exact prime_27140033
  · decide +kernel

theorem prime_4262993544169 : Nat.Prime 4262993544169 := by
  apply nodeValid_prime [2, 3, 19, 53, 179, 36497] ⟨4262993544169, 14, [(2, 3), (3, 4), (19, 1), (53, 1), (179, 1), (36497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
    · exact prime_179
    · exact prime_36497
  · decide +kernel

theorem prime_4266474517427 : Nat.Prime 4266474517427 := by
  apply nodeValid_prime [2, 11, 23, 59, 523, 273253] ⟨4266474517427, 2, [(2, 1), (11, 1), (23, 1), (59, 1), (523, 1), (273253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_59
    · exact prime_523
    · exact prime_273253
  · decide +kernel

theorem prime_4266474615467 : Nat.Prime 4266474615467 := by
  apply nodeValid_prime [2, 7, 304748186819] ⟨4266474615467, 2, [(2, 1), (7, 1), (304748186819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_304748186819
  · decide +kernel

theorem prime_4266474616493 : Nat.Prime 4266474616493 := by
  apply nodeValid_prime [2, 11, 239, 405712687] ⟨4266474616493, 2, [(2, 2), (11, 1), (239, 1), (405712687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_405712687
  · decide +kernel

theorem prime_4269957413327 : Nat.Prime 4269957413327 := by
  apply nodeValid_prime [2, 11, 194088973333] ⟨4269957413327, 5, [(2, 1), (11, 1), (194088973333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_194088973333
  · decide +kernel

theorem prime_4269957413951 : Nat.Prime 4269957413951 := by
  apply nodeValid_prime [2, 5, 85399148279] ⟨4269957413951, 11, [(2, 1), (5, 2), (85399148279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_85399148279
  · decide +kernel

theorem prime_4269957424721 : Nat.Prime 4269957424721 := by
  apply nodeValid_prime [2, 5, 13, 17, 241513429] ⟨4269957424721, 3, [(2, 4), (5, 1), (13, 1), (17, 1), (241513429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_241513429
  · decide +kernel

theorem prime_4273442261467 : Nat.Prime 4273442261467 := by
  apply nodeValid_prime [2, 3, 7, 101748625273] ⟨4273442261467, 2, [(2, 1), (3, 1), (7, 1), (101748625273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101748625273
  · decide +kernel

theorem prime_4273442275393 : Nat.Prime 4273442275393 := by
  apply nodeValid_prime [2, 3, 17, 227, 1922563] ⟨4273442275393, 10, [(2, 6), (3, 2), (17, 1), (227, 1), (1922563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_227
    · exact prime_1922563
  · decide +kernel

theorem prime_4273442275961 : Nat.Prime 4273442275961 := by
  apply nodeValid_prime [2, 5, 11, 13, 109, 623107] ⟨4273442275961, 3, [(2, 3), (5, 1), (11, 2), (13, 1), (109, 1), (623107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_109
    · exact prime_623107
  · decide +kernel

theorem prime_4276928898283 : Nat.Prime 4276928898283 := by
  apply nodeValid_prime [2, 3, 2503, 284786849] ⟨4276928898283, 2, [(2, 1), (3, 1), (2503, 1), (284786849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2503
    · exact prime_284786849
  · decide +kernel

theorem prime_4276928898391 : Nat.Prime 4276928898391 := by
  apply nodeValid_prime [2, 3, 5, 2861, 49830233] ⟨4276928898391, 3, [(2, 1), (3, 1), (5, 1), (2861, 1), (49830233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2861
    · exact prime_49830233
  · decide +kernel

theorem prime_4276929013199 : Nat.Prime 4276929013199 := by
  apply nodeValid_prime [2, 2138464506599] ⟨4276929013199, 13, [(2, 1), (2138464506599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2138464506599
  · decide +kernel

theorem prime_4280417678377 : Nat.Prime 4280417678377 := by
  apply nodeValid_prime [2, 3, 7, 19258259] ⟨4280417678377, 53, [(2, 3), (3, 4), (7, 3), (19258259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19258259
  · decide +kernel

theorem prime_4280417678653 : Nat.Prime 4280417678653 := by
  apply nodeValid_prime [2, 3, 356701473221] ⟨4280417678653, 2, [(2, 2), (3, 1), (356701473221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_356701473221
  · decide +kernel

theorem prime_4280417686651 : Nat.Prime 4280417686651 := by
  apply nodeValid_prime [2, 3, 5, 7, 4076588273] ⟨4280417686651, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (4076588273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_4076588273
  · decide +kernel

theorem prime_4283908120157 : Nat.Prime 4283908120157 := by
  apply nodeValid_prime [2, 7, 252233, 606569] ⟨4283908120157, 2, [(2, 2), (7, 1), (252233, 1), (606569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_252233
    · exact prime_606569
  · decide +kernel

theorem prime_4283908121071 : Nat.Prime 4283908121071 := by
  apply nodeValid_prime [2, 3, 5, 2803, 16981441] ⟨4283908121071, 3, [(2, 1), (3, 2), (5, 1), (2803, 1), (16981441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2803
    · exact prime_16981441
  · decide +kernel

theorem prime_4283908278491 : Nat.Prime 4283908278491 := by
  apply nodeValid_prime [2, 5, 113, 3791069273] ⟨4283908278491, 2, [(2, 1), (5, 1), (113, 1), (3791069273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
    · exact prime_3791069273
  · decide +kernel

theorem prime_4287400792853 : Nat.Prime 4287400792853 := by
  apply nodeValid_prime [2, 19, 23, 109, 223, 100907] ⟨4287400792853, 2, [(2, 2), (19, 1), (23, 1), (109, 1), (223, 1), (100907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_109
    · exact prime_223
    · exact prime_100907
  · decide +kernel

theorem prime_4287400830829 : Nat.Prime 4287400830829 := by
  apply nodeValid_prime [2, 3, 59, 672850099] ⟨4287400830829, 6, [(2, 2), (3, 3), (59, 1), (672850099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_672850099
  · decide +kernel

theorem prime_4287400834543 : Nat.Prime 4287400834543 := by
  apply nodeValid_prime [2, 3, 7, 41, 227, 577, 19009] ⟨4287400834543, 13, [(2, 1), (3, 1), (7, 1), (41, 1), (227, 1), (577, 1), (19009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_227
    · exact prime_577
    · exact prime_19009
  · decide +kernel

theorem prime_4290895233929 : Nat.Prime 4290895233929 := by
  apply nodeValid_prime [2, 31, 151, 114582761] ⟨4290895233929, 3, [(2, 3), (31, 1), (151, 1), (114582761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_151
    · exact prime_114582761
  · decide +kernel

theorem prime_4290895341697 : Nat.Prime 4290895341697 := by
  apply nodeValid_prime [2, 3, 47, 5058491] ⟨4290895341697, 5, [(2, 7), (3, 1), (47, 2), (5058491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_5058491
  · decide +kernel

theorem prime_4290895342037 : Nat.Prime 4290895342037 := by
  apply nodeValid_prime [2, 2333, 459804473] ⟨4290895342037, 2, [(2, 2), (2333, 1), (459804473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2333
    · exact prime_459804473
  · decide +kernel

theorem prime_4294391605841 : Nat.Prime 4294391605841 := by
  apply nodeValid_prime [2, 5, 7, 7668556439] ⟨4294391605841, 3, [(2, 4), (5, 1), (7, 1), (7668556439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7668556439
  · decide +kernel

theorem prime_4294391609951 : Nat.Prime 4294391609951 := by
  apply nodeValid_prime [2, 5, 13, 19, 4021, 86477] ⟨4294391609951, 7, [(2, 1), (5, 2), (13, 1), (19, 1), (4021, 1), (86477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_4021
    · exact prime_86477
  · decide +kernel

theorem prime_4294391610167 : Nat.Prime 4294391610167 := by
  apply nodeValid_prime [2, 7, 306742257869] ⟨4294391610167, 5, [(2, 1), (7, 1), (306742257869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_306742257869
  · decide +kernel

theorem prime_4297889867543 : Nat.Prime 4297889867543 := by
  apply nodeValid_prime [2, 1039111, 2068061] ⟨4297889867543, 5, [(2, 1), (1039111, 1), (2068061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1039111
    · exact prime_2068061
  · decide +kernel

theorem prime_4297889868227 : Nat.Prime 4297889868227 := by
  apply nodeValid_prime [2, 2148944934113] ⟨4297889868227, 2, [(2, 1), (2148944934113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2148944934113
  · decide +kernel

theorem prime_4297889905723 : Nat.Prime 4297889905723 := by
  apply nodeValid_prime [2, 3, 7, 31, 1100330237] ⟨4297889905723, 2, [(2, 1), (3, 2), (7, 1), (31, 1), (1100330237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_1100330237
  · decide +kernel

theorem prime_4301390050651 : Nat.Prime 4301390050651 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 29, 4280629] ⟨4301390050651, 2, [(2, 1), (3, 2), (5, 2), (7, 1), (11, 1), (29, 1), (4280629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_4280629
  · decide +kernel

theorem prime_4301390051929 : Nat.Prime 4301390051929 := by
  apply nodeValid_prime [2, 3, 14029, 473159] ⟨4301390051929, 7, [(2, 3), (3, 4), (14029, 1), (473159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14029
    · exact prime_473159
  · decide +kernel

theorem prime_4301390126281 : Nat.Prime 4301390126281 := by
  apply nodeValid_prime [2, 3, 5, 13, 1009, 1459, 1873] ⟨4301390126281, 33, [(2, 3), (3, 1), (5, 1), (13, 1), (1009, 1), (1459, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1009
    · exact prime_1459
    · exact prime_1873
  · decide +kernel

theorem prime_4304892212111 : Nat.Prime 4304892212111 := by
  apply nodeValid_prime [2, 5, 7, 3769, 16316917] ⟨4304892212111, 7, [(2, 1), (5, 1), (7, 1), (3769, 1), (16316917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3769
    · exact prime_16316917
  · decide +kernel

theorem prime_4304892212977 : Nat.Prime 4304892212977 := by
  apply nodeValid_prime [2, 3, 181081, 495277] ⟨4304892212977, 5, [(2, 4), (3, 1), (181081, 1), (495277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181081
    · exact prime_495277
  · decide +kernel

theorem prime_4304892275687 : Nat.Prime 4304892275687 := by
  apply nodeValid_prime [2, 167, 13619, 946391] ⟨4304892275687, 5, [(2, 1), (167, 1), (13619, 1), (946391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_13619
    · exact prime_946391
  · decide +kernel

theorem prime_4308396306373 : Nat.Prime 4308396306373 := by
  apply nodeValid_prime [2, 3, 31, 101, 38223467] ⟨4308396306373, 2, [(2, 2), (3, 2), (31, 1), (101, 1), (38223467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_101
    · exact prime_38223467
  · decide +kernel

theorem prime_4308396306871 : Nat.Prime 4308396306871 := by
  apply nodeValid_prime [2, 3, 5, 264697, 542557] ⟨4308396306871, 13, [(2, 1), (3, 1), (5, 1), (264697, 1), (542557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_264697
    · exact prime_542557
  · decide +kernel

theorem prime_4308396353057 : Nat.Prime 4308396353057 := by
  apply nodeValid_prime [2, 97, 1388014289] ⟨4308396353057, 3, [(2, 5), (97, 1), (1388014289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1388014289
  · decide +kernel

theorem prime_4311902365699 : Nat.Prime 4311902365699 := by
  apply nodeValid_prime [2, 3, 353, 8447, 241013] ⟨4311902365699, 2, [(2, 1), (3, 1), (353, 1), (8447, 1), (241013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353
    · exact prime_8447
    · exact prime_241013
  · decide +kernel

theorem prime_4311902380367 : Nat.Prime 4311902380367 := by
  apply nodeValid_prime [2, 7, 2861, 107652229] ⟨4311902380367, 7, [(2, 1), (7, 1), (2861, 1), (107652229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2861
    · exact prime_107652229
  · decide +kernel

theorem prime_4311902380579 : Nat.Prime 4311902380579 := by
  apply nodeValid_prime [2, 3, 13, 101, 167, 1481, 2213] ⟨4311902380579, 2, [(2, 1), (3, 1), (13, 1), (101, 1), (167, 1), (1481, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
    · exact prime_167
    · exact prime_1481
    · exact prime_2213
  · decide +kernel

theorem prime_4315410318757 : Nat.Prime 4315410318757 := by
  apply nodeValid_prime [2, 3, 31, 907, 12790039] ⟨4315410318757, 2, [(2, 2), (3, 1), (31, 1), (907, 1), (12790039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_907
    · exact prime_12790039
  · decide +kernel

theorem prime_4315410349309 : Nat.Prime 4315410349309 := by
  apply nodeValid_prime [2, 3, 107, 1120303829] ⟨4315410349309, 7, [(2, 2), (3, 2), (107, 1), (1120303829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_1120303829
  · decide +kernel

theorem prime_4315410350863 : Nat.Prime 4315410350863 := by
  apply nodeValid_prime [2, 3, 13, 23, 29, 82947187] ⟨4315410350863, 3, [(2, 1), (3, 1), (13, 1), (23, 1), (29, 1), (82947187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_29
    · exact prime_82947187
  · decide +kernel

end Sude.Lucas.Generated
