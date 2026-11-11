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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0084

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9181 : Nat.Prime 9181 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨9181, 2, [(2, 2), (3, 3), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_11941 : Nat.Prime 11941 := by
  apply nodeValid_prime [2, 3, 5, 199] ⟨11941, 10, [(2, 2), (3, 1), (5, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
  · decide +kernel

theorem prime_12541 : Nat.Prime 12541 := by
  apply nodeValid_prime [2, 3, 5, 11, 19] ⟨12541, 14, [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_15331 : Nat.Prime 15331 := by
  apply nodeValid_prime [2, 3, 5, 7, 73] ⟨15331, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_18199 : Nat.Prime 18199 := by
  apply nodeValid_prime [2, 3, 337] ⟨18199, 11, [(2, 1), (3, 3), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
  · decide +kernel

theorem prime_20479 : Nat.Prime 20479 := by
  apply nodeValid_prime [2, 3, 3413] ⟨20479, 3, [(2, 1), (3, 1), (3413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3413
  · decide +kernel

theorem prime_23599 : Nat.Prime 23599 := by
  apply nodeValid_prime [2, 3, 19, 23] ⟨23599, 3, [(2, 1), (3, 3), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_24281 : Nat.Prime 24281 := by
  apply nodeValid_prime [2, 5, 607] ⟨24281, 3, [(2, 3), (5, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_607
  · decide +kernel

theorem prime_29483 : Nat.Prime 29483 := by
  apply nodeValid_prime [2, 14741] ⟨29483, 2, [(2, 1), (14741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14741
  · decide +kernel

theorem prime_32467 : Nat.Prime 32467 := by
  apply nodeValid_prime [2, 3, 7, 773] ⟨32467, 2, [(2, 1), (3, 1), (7, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_773
  · decide +kernel

theorem prime_34673 : Nat.Prime 34673 := by
  apply nodeValid_prime [2, 11, 197] ⟨34673, 3, [(2, 4), (11, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_197
  · decide +kernel

theorem prime_40853 : Nat.Prime 40853 := by
  apply nodeValid_prime [2, 7, 1459] ⟨40853, 2, [(2, 2), (7, 1), (1459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1459
  · decide +kernel

theorem prime_42787 : Nat.Prime 42787 := by
  apply nodeValid_prime [2, 3, 2377] ⟨42787, 5, [(2, 1), (3, 2), (2377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2377
  · decide +kernel

theorem prime_43499 : Nat.Prime 43499 := by
  apply nodeValid_prime [2, 7, 13, 239] ⟨43499, 2, [(2, 1), (7, 1), (13, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_239
  · decide +kernel

theorem prime_47057 : Nat.Prime 47057 := by
  apply nodeValid_prime [2, 17, 173] ⟨47057, 3, [(2, 4), (17, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_173
  · decide +kernel

theorem prime_51197 : Nat.Prime 51197 := by
  apply nodeValid_prime [2, 12799] ⟨51197, 2, [(2, 2), (12799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12799
  · decide +kernel

theorem prime_62743 : Nat.Prime 62743 := by
  apply nodeValid_prime [2, 3, 10457] ⟨62743, 7, [(2, 1), (3, 1), (10457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10457
  · decide +kernel

theorem prime_63029 : Nat.Prime 63029 := by
  apply nodeValid_prime [2, 7, 2251] ⟨63029, 2, [(2, 2), (7, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2251
  · decide +kernel

theorem prime_65599 : Nat.Prime 65599 := by
  apply nodeValid_prime [2, 3, 13, 29] ⟨65599, 3, [(2, 1), (3, 1), (13, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_67447 : Nat.Prime 67447 := by
  apply nodeValid_prime [2, 3, 1249] ⟨67447, 3, [(2, 1), (3, 3), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1249
  · decide +kernel

theorem prime_81707 : Nat.Prime 81707 := by
  apply nodeValid_prime [2, 40853] ⟨81707, 2, [(2, 1), (40853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40853
  · decide +kernel

theorem prime_83207 : Nat.Prime 83207 := by
  apply nodeValid_prime [2, 41603] ⟨83207, 5, [(2, 1), (41603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41603
  · decide +kernel

theorem prime_89101 : Nat.Prime 89101 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨89101, 2, [(2, 2), (3, 4), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_107839 : Nat.Prime 107839 := by
  apply nodeValid_prime [2, 3, 1997] ⟨107839, 15, [(2, 1), (3, 3), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1997
  · decide +kernel

theorem prime_120391 : Nat.Prime 120391 := by
  apply nodeValid_prime [2, 3, 5, 4013] ⟨120391, 21, [(2, 1), (3, 1), (5, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4013
  · decide +kernel

theorem prime_132499 : Nat.Prime 132499 := by
  apply nodeValid_prime [2, 3, 17, 433] ⟨132499, 2, [(2, 1), (3, 2), (17, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_433
  · decide +kernel

theorem prime_133493 : Nat.Prime 133493 := by
  apply nodeValid_prime [2, 23, 1451] ⟨133493, 3, [(2, 2), (23, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1451
  · decide +kernel

theorem prime_133543 : Nat.Prime 133543 := by
  apply nodeValid_prime [2, 3, 2473] ⟨133543, 3, [(2, 1), (3, 3), (2473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2473
  · decide +kernel

theorem prime_145687 : Nat.Prime 145687 := by
  apply nodeValid_prime [2, 3, 24281] ⟨145687, 3, [(2, 1), (3, 1), (24281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24281
  · decide +kernel

theorem prime_157273 : Nat.Prime 157273 := by
  apply nodeValid_prime [2, 3, 6553] ⟨157273, 5, [(2, 3), (3, 1), (6553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6553
  · decide +kernel

theorem prime_207811 : Nat.Prime 207811 := by
  apply nodeValid_prime [2, 3, 5, 2309] ⟨207811, 3, [(2, 1), (3, 2), (5, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2309
  · decide +kernel

theorem prime_211927 : Nat.Prime 211927 := by
  apply nodeValid_prime [2, 3, 11, 13, 19] ⟨211927, 3, [(2, 1), (3, 1), (11, 1), (13, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_217367 : Nat.Prime 217367 := by
  apply nodeValid_prime [2, 251, 433] ⟨217367, 5, [(2, 1), (251, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_433
  · decide +kernel

theorem prime_234809 : Nat.Prime 234809 := by
  apply nodeValid_prime [2, 7, 599] ⟨234809, 3, [(2, 3), (7, 2), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_599
  · decide +kernel

theorem prime_252583 : Nat.Prime 252583 := by
  apply nodeValid_prime [2, 3, 11, 43, 89] ⟨252583, 3, [(2, 1), (3, 1), (11, 1), (43, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_89
  · decide +kernel

theorem prime_282913 : Nat.Prime 282913 := by
  apply nodeValid_prime [2, 3, 7, 421] ⟨282913, 5, [(2, 5), (3, 1), (7, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_421
  · decide +kernel

theorem prime_308597 : Nat.Prime 308597 := by
  apply nodeValid_prime [2, 179, 431] ⟨308597, 2, [(2, 2), (179, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_431
  · decide +kernel

theorem prime_318001 : Nat.Prime 318001 := by
  apply nodeValid_prime [2, 3, 5, 53] ⟨318001, 13, [(2, 4), (3, 1), (5, 3), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel

theorem prime_334511 : Nat.Prime 334511 := by
  apply nodeValid_prime [2, 5, 11, 3041] ⟨334511, 13, [(2, 1), (5, 1), (11, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3041
  · decide +kernel

theorem prime_363497 : Nat.Prime 363497 := by
  apply nodeValid_prime [2, 7, 6491] ⟨363497, 5, [(2, 3), (7, 1), (6491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6491
  · decide +kernel

theorem prime_416077 : Nat.Prime 416077 := by
  apply nodeValid_prime [2, 3, 34673] ⟨416077, 5, [(2, 2), (3, 1), (34673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34673
  · decide +kernel

theorem prime_530731 : Nat.Prime 530731 := by
  apply nodeValid_prime [2, 3, 5, 5897] ⟨530731, 3, [(2, 1), (3, 2), (5, 1), (5897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5897
  · decide +kernel

theorem prime_669023 : Nat.Prime 669023 := by
  apply nodeValid_prime [2, 334511] ⟨669023, 5, [(2, 1), (334511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_334511
  · decide +kernel

theorem prime_836807 : Nat.Prime 836807 := by
  apply nodeValid_prime [2, 71, 83] ⟨836807, 5, [(2, 1), (71, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_83
  · decide +kernel

theorem prime_882577 : Nat.Prime 882577 := by
  apply nodeValid_prime [2, 3, 227] ⟨882577, 7, [(2, 4), (3, 5), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
  · decide +kernel

theorem prime_1089299 : Nat.Prime 1089299 := by
  apply nodeValid_prime [2, 7, 29, 2683] ⟨1089299, 2, [(2, 1), (7, 1), (29, 1), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_2683
  · decide +kernel

theorem prime_1132753 : Nat.Prime 1132753 := by
  apply nodeValid_prime [2, 3, 23599] ⟨1132753, 7, [(2, 4), (3, 1), (23599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23599
  · decide +kernel

theorem prime_1231771 : Nat.Prime 1231771 := by
  apply nodeValid_prime [2, 3, 5, 19, 2161] ⟨1231771, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_2161
  · decide +kernel

theorem prime_1335431 : Nat.Prime 1335431 := by
  apply nodeValid_prime [2, 5, 133543] ⟨1335431, 11, [(2, 1), (5, 1), (133543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_133543
  · decide +kernel

theorem prime_1562527 : Nat.Prime 1562527 := by
  apply nodeValid_prime [2, 3, 7, 12401] ⟨1562527, 3, [(2, 1), (3, 2), (7, 1), (12401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_12401
  · decide +kernel

theorem prime_2178599 : Nat.Prime 2178599 := by
  apply nodeValid_prime [2, 1089299] ⟨2178599, 11, [(2, 1), (1089299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1089299
  · decide +kernel

theorem prime_2468777 : Nat.Prime 2468777 := by
  apply nodeValid_prime [2, 308597] ⟨2468777, 3, [(2, 3), (308597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_308597
  · decide +kernel

theorem prime_2509811 : Nat.Prime 2509811 := by
  apply nodeValid_prime [2, 5, 419, 599] ⟨2509811, 6, [(2, 1), (5, 1), (419, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_419
    · exact prime_599
  · decide +kernel

theorem prime_2738231 : Nat.Prime 2738231 := by
  apply nodeValid_prime [2, 5, 11, 31, 73] ⟨2738231, 17, [(2, 1), (5, 1), (11, 2), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_2797303 : Nat.Prime 2797303 := by
  apply nodeValid_prime [2, 3, 127, 3671] ⟨2797303, 3, [(2, 1), (3, 1), (127, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_3671
  · decide +kernel

theorem prime_2907977 : Nat.Prime 2907977 := by
  apply nodeValid_prime [2, 363497] ⟨2907977, 3, [(2, 3), (363497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_363497
  · decide +kernel

theorem prime_3004877 : Nat.Prime 3004877 := by
  apply nodeValid_prime [2, 7, 15331] ⟨3004877, 2, [(2, 2), (7, 2), (15331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15331
  · decide +kernel

theorem prime_3130229 : Nat.Prime 3130229 := by
  apply nodeValid_prime [2, 43, 18199] ⟨3130229, 2, [(2, 2), (43, 1), (18199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_18199
  · decide +kernel

theorem prime_3851377 : Nat.Prime 3851377 := by
  apply nodeValid_prime [2, 3, 19, 41, 103] ⟨3851377, 7, [(2, 4), (3, 1), (19, 1), (41, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_103
  · decide +kernel

theorem prime_4014139 : Nat.Prime 4014139 := by
  apply nodeValid_prime [2, 3, 669023] ⟨4014139, 3, [(2, 1), (3, 1), (669023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_669023
  · decide +kernel

theorem prime_4183381 : Nat.Prime 4183381 := by
  apply nodeValid_prime [2, 3, 5, 61, 127] ⟨4183381, 7, [(2, 2), (3, 3), (5, 1), (61, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_127
  · decide +kernel

theorem prime_4347341 : Nat.Prime 4347341 := by
  apply nodeValid_prime [2, 5, 217367] ⟨4347341, 2, [(2, 2), (5, 1), (217367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_217367
  · decide +kernel

theorem prime_4659229 : Nat.Prime 4659229 := by
  apply nodeValid_prime [2, 3, 7, 6163] ⟨4659229, 2, [(2, 2), (3, 3), (7, 1), (6163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6163
  · decide +kernel

theorem prime_6202121 : Nat.Prime 6202121 := by
  apply nodeValid_prime [2, 5, 47, 3299] ⟨6202121, 6, [(2, 3), (5, 1), (47, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_3299
  · decide +kernel

theorem prime_9622909 : Nat.Prime 9622909 := by
  apply nodeValid_prime [2, 3, 89101] ⟨9622909, 2, [(2, 2), (3, 3), (89101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89101
  · decide +kernel

theorem prime_10534369 : Nat.Prime 10534369 := by
  apply nodeValid_prime [2, 3, 13, 23, 367] ⟨10534369, 11, [(2, 5), (3, 1), (13, 1), (23, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_367
  · decide +kernel

theorem prime_12871321 : Nat.Prime 12871321 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 199] ⟨12871321, 13, [(2, 3), (3, 1), (5, 1), (7, 2), (11, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_199
  · decide +kernel

theorem prime_12988603 : Nat.Prime 12988603 := by
  apply nodeValid_prime [2, 3, 11, 65599] ⟨12988603, 2, [(2, 1), (3, 2), (11, 1), (65599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_65599
  · decide +kernel

theorem prime_17394079 : Nat.Prime 17394079 := by
  apply nodeValid_prime [2, 3, 13, 269, 829] ⟨17394079, 3, [(2, 1), (3, 1), (13, 1), (269, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_269
    · exact prime_829
  · decide +kernel

theorem prime_18434821 : Nat.Prime 18434821 := by
  apply nodeValid_prime [2, 3, 5, 113, 2719] ⟨18434821, 2, [(2, 2), (3, 1), (5, 1), (113, 1), (2719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_2719
  · decide +kernel

theorem prime_22811483 : Nat.Prime 22811483 := by
  apply nodeValid_prime [2, 1693, 6737] ⟨22811483, 2, [(2, 1), (1693, 1), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1693
    · exact prime_6737
  · decide +kernel

theorem prime_23108263 : Nat.Prime 23108263 := by
  apply nodeValid_prime [2, 3, 3851377] ⟨23108263, 5, [(2, 1), (3, 1), (3851377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3851377
  · decide +kernel

theorem prime_25100287 : Nat.Prime 25100287 := by
  apply nodeValid_prime [2, 3, 4183381] ⟨25100287, 3, [(2, 1), (3, 1), (4183381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4183381
  · decide +kernel

theorem prime_29327351 : Nat.Prime 29327351 := by
  apply nodeValid_prime [2, 5, 13, 45119] ⟨29327351, 11, [(2, 1), (5, 2), (13, 1), (45119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_45119
  · decide +kernel

theorem prime_33970969 : Nat.Prime 33970969 := by
  apply nodeValid_prime [2, 3, 157273] ⟨33970969, 11, [(2, 3), (3, 3), (157273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157273
  · decide +kernel

theorem prime_42463237 : Nat.Prime 42463237 := by
  apply nodeValid_prime [2, 3, 241, 14683] ⟨42463237, 2, [(2, 2), (3, 1), (241, 1), (14683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_14683
  · decide +kernel

theorem prime_45638503 : Nat.Prime 45638503 := by
  apply nodeValid_prime [2, 3, 7, 13, 11941] ⟨45638503, 5, [(2, 1), (3, 1), (7, 2), (13, 1), (11941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_11941
  · decide +kernel

theorem prime_50535847 : Nat.Prime 50535847 := by
  apply nodeValid_prime [2, 3, 337, 2777] ⟨50535847, 3, [(2, 1), (3, 3), (337, 1), (2777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
    · exact prime_2777
  · decide +kernel

theorem prime_57705121 : Nat.Prime 57705121 := by
  apply nodeValid_prime [2, 3, 5, 11, 3643] ⟨57705121, 7, [(2, 5), (3, 2), (5, 1), (11, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_3643
  · decide +kernel

theorem prime_60834869 : Nat.Prime 60834869 := by
  apply nodeValid_prime [2, 2729, 5573] ⟨60834869, 2, [(2, 2), (2729, 1), (5573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2729
    · exact prime_5573
  · decide +kernel

theorem prime_76283531 : Nat.Prime 76283531 := by
  apply nodeValid_prime [2, 5, 149, 51197] ⟨76283531, 2, [(2, 1), (5, 1), (149, 1), (51197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_51197
  · decide +kernel

theorem prime_93145981 : Nat.Prime 93145981 := by
  apply nodeValid_prime [2, 3, 5, 19, 81707] ⟨93145981, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (81707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_81707
  · decide +kernel

theorem prime_110220917 : Nat.Prime 110220917 := by
  apply nodeValid_prime [2, 13, 1319, 1607] ⟨110220917, 2, [(2, 2), (13, 1), (1319, 1), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1319
    · exact prime_1607
  · decide +kernel

theorem prime_111821497 : Nat.Prime 111821497 := by
  apply nodeValid_prime [2, 3, 4659229] ⟨111821497, 5, [(2, 3), (3, 1), (4659229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4659229
  · decide +kernel

theorem prime_120982717 : Nat.Prime 120982717 := by
  apply nodeValid_prime [2, 3, 971, 3461] ⟨120982717, 2, [(2, 2), (3, 2), (971, 1), (3461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_971
    · exact prime_3461
  · decide +kernel

theorem prime_129311471 : Nat.Prime 129311471 := by
  apply nodeValid_prime [2, 5, 73, 307, 577] ⟨129311471, 7, [(2, 1), (5, 1), (73, 1), (307, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_307
    · exact prime_577
  · decide +kernel

theorem prime_167361401 : Nat.Prime 167361401 := by
  apply nodeValid_prime [2, 5, 836807] ⟨167361401, 3, [(2, 3), (5, 2), (836807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_836807
  · decide +kernel

theorem prime_212520857 : Nat.Prime 212520857 := by
  apply nodeValid_prime [2, 199, 133493] ⟨212520857, 3, [(2, 3), (199, 1), (133493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_133493
  · decide +kernel

theorem prime_339302863 : Nat.Prime 339302863 := by
  apply nodeValid_prime [2, 3, 61, 309019] ⟨339302863, 3, [(2, 1), (3, 2), (61, 1), (309019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_309019
  · decide +kernel

theorem prime_348565733 : Nat.Prime 348565733 := by
  apply nodeValid_prime [2, 29, 3004877] ⟨348565733, 2, [(2, 2), (29, 1), (3004877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3004877
  · decide +kernel

theorem prime_371436049 : Nat.Prime 371436049 := by
  apply nodeValid_prime [2, 3, 31, 83207] ⟨371436049, 7, [(2, 4), (3, 2), (31, 1), (83207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_83207
  · decide +kernel

theorem prime_384617143 : Nat.Prime 384617143 := by
  apply nodeValid_prime [2, 3, 7, 13, 234809] ⟨384617143, 5, [(2, 1), (3, 2), (7, 1), (13, 1), (234809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_234809
  · decide +kernel

theorem prime_449317801 : Nat.Prime 449317801 := by
  apply nodeValid_prime [2, 3, 5, 83207] ⟨449317801, 47, [(2, 3), (3, 3), (5, 2), (83207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83207
  · decide +kernel

theorem prime_610268249 : Nat.Prime 610268249 := by
  apply nodeValid_prime [2, 76283531] ⟨610268249, 3, [(2, 3), (76283531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76283531
  · decide +kernel

theorem prime_1009620229 : Nat.Prime 1009620229 := by
  apply nodeValid_prime [2, 3, 397, 211927] ⟨1009620229, 2, [(2, 2), (3, 1), (397, 1), (211927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_211927
  · decide +kernel

theorem prime_1312522681 : Nat.Prime 1312522681 := by
  apply nodeValid_prime [2, 3, 5, 7, 1562527] ⟨1312522681, 22, [(2, 3), (3, 1), (5, 1), (7, 1), (1562527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1562527
  · decide +kernel

theorem prime_1349322383 : Nat.Prime 1349322383 := by
  apply nodeValid_prime [2, 29, 41, 647, 877] ⟨1349322383, 5, [(2, 1), (29, 1), (41, 1), (647, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_41
    · exact prime_647
    · exact prime_877
  · decide +kernel

theorem prime_1555329511 : Nat.Prime 1555329511 := by
  apply nodeValid_prime [2, 3, 5, 7, 2468777] ⟨1555329511, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (2468777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2468777
  · decide +kernel

theorem prime_3080064601 : Nat.Prime 3080064601 := by
  apply nodeValid_prime [2, 3, 5, 349, 4903] ⟨3080064601, 7, [(2, 3), (3, 2), (5, 2), (349, 1), (4903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_349
    · exact prime_4903
  · decide +kernel

theorem prime_6477035801 : Nat.Prime 6477035801 := by
  apply nodeValid_prime [2, 5, 269, 120391] ⟨6477035801, 3, [(2, 3), (5, 2), (269, 1), (120391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_120391
  · decide +kernel

theorem prime_6809204279 : Nat.Prime 6809204279 := by
  apply nodeValid_prime [2, 59, 57705121] ⟨6809204279, 11, [(2, 1), (59, 1), (57705121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_57705121
  · decide +kernel

theorem prime_11380147517 : Nat.Prime 11380147517 := by
  apply nodeValid_prime [2, 67, 42463237] ⟨11380147517, 2, [(2, 2), (67, 1), (42463237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_42463237
  · decide +kernel

theorem prime_12079400791 : Nat.Prime 12079400791 := by
  apply nodeValid_prime [2, 3, 5, 31, 12988603] ⟨12079400791, 15, [(2, 1), (3, 1), (5, 1), (31, 1), (12988603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_12988603
  · decide +kernel

theorem prime_16549581557 : Nat.Prime 16549581557 := by
  apply nodeValid_prime [2, 37, 111821497] ⟨16549581557, 2, [(2, 2), (37, 1), (111821497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_111821497
  · decide +kernel

theorem prime_20587800403 : Nat.Prime 20587800403 := by
  apply nodeValid_prime [2, 3, 13, 29327351] ⟨20587800403, 2, [(2, 1), (3, 3), (13, 1), (29327351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29327351
  · decide +kernel

theorem prime_21000362897 : Nat.Prime 21000362897 := by
  apply nodeValid_prime [2, 1312522681] ⟨21000362897, 3, [(2, 4), (1312522681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1312522681
  · decide +kernel

theorem prime_38577322057 : Nat.Prime 38577322057 := by
  apply nodeValid_prime [2, 3, 7, 13, 23, 181, 4243] ⟨38577322057, 10, [(2, 3), (3, 1), (7, 1), (13, 1), (23, 1), (181, 1), (4243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_181
    · exact prime_4243
  · decide +kernel

theorem prime_78001570291 : Nat.Prime 78001570291 := by
  apply nodeValid_prime [2, 3, 5, 7, 371436049] ⟨78001570291, 13, [(2, 1), (3, 1), (5, 1), (7, 1), (371436049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_371436049
  · decide +kernel

theorem prime_128463268867 : Nat.Prime 128463268867 := by
  apply nodeValid_prime [2, 3, 853, 25100287] ⟨128463268867, 2, [(2, 1), (3, 1), (853, 1), (25100287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853
    · exact prime_25100287
  · decide +kernel

theorem prime_164838753509 : Nat.Prime 164838753509 := by
  apply nodeValid_prime [2, 11, 13, 2089, 12541] ⟨164838753509, 2, [(2, 2), (11, 2), (13, 1), (2089, 1), (12541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_2089
    · exact prime_12541
  · decide +kernel

theorem prime_234700924603 : Nat.Prime 234700924603 := by
  apply nodeValid_prime [2, 3, 643, 60834869] ⟨234700924603, 2, [(2, 1), (3, 1), (643, 1), (60834869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_643
    · exact prime_60834869
  · decide +kernel

theorem prime_294830478827 : Nat.Prime 294830478827 := by
  apply nodeValid_prime [2, 13, 881, 12871321] ⟨294830478827, 2, [(2, 1), (13, 1), (881, 1), (12871321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_881
    · exact prime_12871321
  · decide +kernel

theorem prime_385773220571 : Nat.Prime 385773220571 := by
  apply nodeValid_prime [2, 5, 38577322057] ⟨385773220571, 2, [(2, 1), (5, 1), (38577322057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_38577322057
  · decide +kernel

theorem prime_386156902931 : Nat.Prime 386156902931 := by
  apply nodeValid_prime [2, 5, 92809, 416077] ⟨386156902931, 2, [(2, 1), (5, 1), (92809, 1), (416077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_92809
    · exact prime_416077
  · decide +kernel

theorem prime_387694167937 : Nat.Prime 387694167937 := by
  apply nodeValid_prime [2, 3, 1009620229] ⟨387694167937, 10, [(2, 7), (3, 1), (1009620229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1009620229
  · decide +kernel

theorem prime_583853372959 : Nat.Prime 583853372959 := by
  apply nodeValid_prime [2, 3, 4211, 23108263] ⟨583853372959, 3, [(2, 1), (3, 1), (4211, 1), (23108263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4211
    · exact prime_23108263
  · decide +kernel

theorem prime_585011776903 : Nat.Prime 585011776903 := by
  apply nodeValid_prime [2, 3, 7, 31, 449317801] ⟨585011776903, 7, [(2, 1), (3, 1), (7, 1), (31, 1), (449317801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_449317801
  · decide +kernel

theorem prime_2303152371727 : Nat.Prime 2303152371727 := by
  apply nodeValid_prime [2, 3, 17, 37, 610268249] ⟨2303152371727, 3, [(2, 1), (3, 1), (17, 1), (37, 1), (610268249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_610268249
  · decide +kernel

theorem prime_2303152398089 : Nat.Prime 2303152398089 := by
  apply nodeValid_prime [2, 31, 151, 829, 74189] ⟨2303152398089, 3, [(2, 3), (31, 1), (151, 1), (829, 1), (74189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_151
    · exact prime_829
    · exact prime_74189
  · decide +kernel

theorem prime_2305446655153 : Nat.Prime 2305446655153 := by
  apply nodeValid_prime [2, 3, 397, 120982717] ⟨2305446655153, 10, [(2, 4), (3, 1), (397, 1), (120982717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_120982717
  · decide +kernel

theorem prime_2305446655651 : Nat.Prime 2305446655651 := by
  apply nodeValid_prime [2, 3, 5, 1459, 10534369] ⟨2305446655651, 2, [(2, 1), (3, 1), (5, 2), (1459, 1), (10534369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1459
    · exact prime_10534369
  · decide +kernel

theorem prime_2305446655693 : Nat.Prime 2305446655693 := by
  apply nodeValid_prime [2, 3, 19, 8209, 1231771] ⟨2305446655693, 2, [(2, 2), (3, 1), (19, 1), (8209, 1), (1231771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_8209
    · exact prime_1231771
  · decide +kernel

theorem prime_2307742496441 : Nat.Prime 2307742496441 := by
  apply nodeValid_prime [2, 5, 23, 577, 4347341] ⟨2307742496441, 3, [(2, 3), (5, 1), (23, 1), (577, 1), (4347341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_577
    · exact prime_4347341
  · decide +kernel

theorem prime_2307742548877 : Nat.Prime 2307742548877 := by
  apply nodeValid_prime [2, 3, 20479, 3130229] ⟨2307742548877, 2, [(2, 2), (3, 2), (20479, 1), (3130229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20479
    · exact prime_3130229
  · decide +kernel

theorem prime_2307742549127 : Nat.Prime 2307742549127 := by
  apply nodeValid_prime [2, 7, 164838753509] ⟨2307742549127, 5, [(2, 1), (7, 1), (164838753509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_164838753509
  · decide +kernel

theorem prime_2310039894251 : Nat.Prime 2310039894251 := by
  apply nodeValid_prime [2, 5, 11, 17851, 47057] ⟨2310039894251, 10, [(2, 1), (5, 3), (11, 1), (17851, 1), (47057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17851
    · exact prime_47057
  · decide +kernel

theorem prime_2310039918671 : Nat.Prime 2310039918671 := by
  apply nodeValid_prime [2, 5, 11, 21000362897] ⟨2310039918671, 11, [(2, 1), (5, 1), (11, 1), (21000362897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_21000362897
  · decide +kernel

theorem prime_2310039919697 : Nat.Prime 2310039919697 := by
  apply nodeValid_prime [2, 107, 1349322383] ⟨2310039919697, 3, [(2, 4), (107, 1), (1349322383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_1349322383
  · decide +kernel

theorem prime_2312338835413 : Nat.Prime 2312338835413 := by
  apply nodeValid_prime [2, 3, 29483, 2178599] ⟨2312338835413, 5, [(2, 2), (3, 2), (29483, 1), (2178599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29483
    · exact prime_2178599
  · decide +kernel

theorem prime_2312338839431 : Nat.Prime 2312338839431 := by
  apply nodeValid_prime [2, 5, 347, 499, 1335431] ⟨2312338839431, 22, [(2, 1), (5, 1), (347, 1), (499, 1), (1335431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_347
    · exact prime_499
    · exact prime_1335431
  · decide +kernel

theorem prime_2312338839607 : Nat.Prime 2312338839607 := by
  apply nodeValid_prime [2, 3, 128463268867] ⟨2312338839607, 5, [(2, 1), (3, 2), (128463268867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_128463268867
  · decide +kernel

theorem prime_2314639257001 : Nat.Prime 2314639257001 := by
  apply nodeValid_prime [2, 3, 5, 7, 110220917] ⟨2314639257001, 13, [(2, 3), (3, 1), (5, 3), (7, 1), (110220917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_110220917
  · decide +kernel

theorem prime_2314639257439 : Nat.Prime 2314639257439 := by
  apply nodeValid_prime [2, 3, 31, 167, 691, 107839] ⟨2314639257439, 6, [(2, 1), (3, 1), (31, 1), (167, 1), (691, 1), (107839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_167
    · exact prime_691
    · exact prime_107839
  · decide +kernel

theorem prime_2314639323427 : Nat.Prime 2314639323427 := by
  apply nodeValid_prime [2, 3, 385773220571] ⟨2314639323427, 3, [(2, 1), (3, 1), (385773220571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_385773220571
  · decide +kernel

theorem prime_2316941362973 : Nat.Prime 2316941362973 := by
  apply nodeValid_prime [2, 409, 9721, 145687] ⟨2316941362973, 2, [(2, 2), (409, 1), (9721, 1), (145687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_9721
    · exact prime_145687
  · decide +kernel

theorem prime_2316941417587 : Nat.Prime 2316941417587 := by
  apply nodeValid_prime [2, 3, 386156902931] ⟨2316941417587, 2, [(2, 1), (3, 1), (386156902931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_386156902931
  · decide +kernel

theorem prime_2316941417981 : Nat.Prime 2316941417981 := by
  apply nodeValid_prime [2, 5, 7, 16549581557] ⟨2316941417981, 10, [(2, 2), (5, 1), (7, 1), (16549581557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_16549581557
  · decide +kernel

theorem prime_2319244951873 : Nat.Prime 2319244951873 := by
  apply nodeValid_prime [2, 3, 12079400791] ⟨2319244951873, 5, [(2, 6), (3, 1), (12079400791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12079400791
  · decide +kernel

theorem prime_2319244952249 : Nat.Prime 2319244952249 := by
  apply nodeValid_prime [2, 7, 677, 907, 67447] ⟨2319244952249, 3, [(2, 3), (7, 1), (677, 1), (907, 1), (67447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_677
    · exact prime_907
    · exact prime_67447
  · decide +kernel

theorem prime_2319244953317 : Nat.Prime 2319244953317 := by
  apply nodeValid_prime [2, 383, 5351, 282913] ⟨2319244953317, 2, [(2, 2), (383, 1), (5351, 1), (282913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_5351
    · exact prime_282913
  · decide +kernel

theorem prime_2321550076751 : Nat.Prime 2321550076751 := by
  apply nodeValid_prime [2, 5, 17497, 530731] ⟨2321550076751, 17, [(2, 1), (5, 3), (17497, 1), (530731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17497
    · exact prime_530731
  · decide +kernel

theorem prime_2321550076891 : Nat.Prime 2321550076891 := by
  apply nodeValid_prime [2, 3, 5, 11, 2803, 2509811] ⟨2321550076891, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (2803, 1), (2509811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2803
    · exact prime_2509811
  · decide +kernel

theorem prime_2321550093469 : Nat.Prime 2321550093469 := by
  apply nodeValid_prime [2, 3, 17, 11380147517] ⟨2321550093469, 2, [(2, 2), (3, 1), (17, 1), (11380147517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_11380147517
  · decide +kernel

theorem prime_2323856665619 : Nat.Prime 2323856665619 := by
  apply nodeValid_prime [2, 63029, 18434821] ⟨2323856665619, 2, [(2, 1), (63029, 1), (18434821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_63029
    · exact prime_18434821
  · decide +kernel

theorem prime_2323856778007 : Nat.Prime 2323856778007 := by
  apply nodeValid_prime [2, 3, 19, 53, 384617143] ⟨2323856778007, 3, [(2, 1), (3, 1), (19, 1), (53, 1), (384617143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_53
    · exact prime_384617143
  · decide +kernel

theorem prime_2326165007623 : Nat.Prime 2326165007623 := by
  apply nodeValid_prime [2, 3, 387694167937] ⟨2326165007623, 3, [(2, 1), (3, 1), (387694167937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_387694167937
  · decide +kernel

theorem prime_2326165037411 : Nat.Prime 2326165037411 := by
  apply nodeValid_prime [2, 5, 4603, 50535847] ⟨2326165037411, 2, [(2, 1), (5, 1), (4603, 1), (50535847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4603
    · exact prime_50535847
  · decide +kernel

theorem prime_2326165038389 : Nat.Prime 2326165038389 := by
  apply nodeValid_prime [2, 223, 271, 9622909] ⟨2326165038389, 2, [(2, 2), (223, 1), (271, 1), (9622909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_271
    · exact prime_9622909
  · decide +kernel

theorem prime_2328474777173 : Nat.Prime 2328474777173 := by
  apply nodeValid_prime [2, 79, 769, 2383, 4021] ⟨2328474777173, 2, [(2, 2), (79, 1), (769, 1), (2383, 1), (4021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_769
    · exact prime_2383
    · exact prime_4021
  · decide +kernel

theorem prime_2328474778117 : Nat.Prime 2328474778117 := by
  apply nodeValid_prime [2, 3, 252583, 768221] ⟨2328474778117, 5, [(2, 2), (3, 1), (252583, 1), (768221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_252583
    · exact prime_768221
  · decide +kernel

theorem prime_2328474784577 : Nat.Prime 2328474784577 := by
  apply nodeValid_prime [2, 23, 31849, 49667] ⟨2328474784577, 3, [(2, 6), (23, 1), (31849, 1), (49667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31849
    · exact prime_49667
  · decide +kernel

theorem prime_2330786087009 : Nat.Prime 2330786087009 := by
  apply nodeValid_prime [2, 31, 103, 22811483] ⟨2330786087009, 3, [(2, 5), (31, 1), (103, 1), (22811483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_103
    · exact prime_22811483
  · decide +kernel

theorem prime_2330786087153 : Nat.Prime 2330786087153 := by
  apply nodeValid_prime [2, 53, 6899, 7517] ⟨2330786087153, 3, [(2, 4), (53, 2), (6899, 1), (7517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_6899
    · exact prime_7517
  · decide +kernel

theorem prime_2330786124479 : Nat.Prime 2330786124479 := by
  apply nodeValid_prime [2, 7, 61, 43499, 62743] ⟨2330786124479, 7, [(2, 1), (7, 1), (61, 1), (43499, 1), (62743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_43499
    · exact prime_62743
  · decide +kernel

theorem prime_2333099026871 : Nat.Prime 2333099026871 := by
  apply nodeValid_prime [2, 5, 80231, 2907977] ⟨2333099026871, 7, [(2, 1), (5, 1), (80231, 1), (2907977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_80231
    · exact prime_2907977
  · decide +kernel

theorem prime_2333099100203 : Nat.Prime 2333099100203 := by
  apply nodeValid_prime [2, 13, 409, 2879, 76207] ⟨2333099100203, 2, [(2, 1), (13, 1), (409, 1), (2879, 1), (76207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_409
    · exact prime_2879
    · exact prime_76207
  · decide +kernel

theorem prime_2333099101573 : Nat.Prime 2333099101573 := by
  apply nodeValid_prime [2, 3, 54347, 132499] ⟨2333099101573, 6, [(2, 2), (3, 4), (54347, 1), (132499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54347
    · exact prime_132499
  · decide +kernel

theorem prime_2335413475517 : Nat.Prime 2335413475517 := by
  apply nodeValid_prime [2, 11, 1163, 45638503] ⟨2335413475517, 2, [(2, 2), (11, 1), (1163, 1), (45638503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1163
    · exact prime_45638503
  · decide +kernel

theorem prime_2335413477011 : Nat.Prime 2335413477011 := by
  apply nodeValid_prime [2, 5, 19, 733, 882577] ⟨2335413477011, 2, [(2, 1), (5, 1), (19, 2), (733, 1), (882577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_733
    · exact prime_882577
  · decide +kernel

theorem prime_2335413491837 : Nat.Prime 2335413491837 := by
  apply nodeValid_prime [2, 583853372959] ⟨2335413491837, 2, [(2, 2), (583853372959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_583853372959
  · decide +kernel

theorem prime_2337729427001 : Nat.Prime 2337729427001 := by
  apply nodeValid_prime [2, 5, 11, 212520857] ⟨2337729427001, 3, [(2, 3), (5, 3), (11, 1), (212520857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_212520857
  · decide +kernel

theorem prime_2337729429443 : Nat.Prime 2337729429443 := by
  apply nodeValid_prime [2, 11, 41, 149, 17394079] ⟨2337729429443, 2, [(2, 1), (11, 1), (41, 1), (149, 1), (17394079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_149
    · exact prime_17394079
  · decide +kernel

theorem prime_2337729517751 : Nat.Prime 2337729517751 := by
  apply nodeValid_prime [2, 5, 11, 26183, 32467] ⟨2337729517751, 11, [(2, 1), (5, 3), (11, 1), (26183, 1), (32467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_26183
    · exact prime_32467
  · decide +kernel

theorem prime_2340047107613 : Nat.Prime 2340047107613 := by
  apply nodeValid_prime [2, 585011776903] ⟨2340047107613, 2, [(2, 2), (585011776903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_585011776903
  · decide +kernel

theorem prime_2340047108731 : Nat.Prime 2340047108731 := by
  apply nodeValid_prime [2, 3, 5, 78001570291] ⟨2340047108731, 2, [(2, 1), (3, 1), (5, 1), (78001570291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_78001570291
  · decide +kernel

theorem prime_2340047108783 : Nat.Prime 2340047108783 := by
  apply nodeValid_prime [2, 6991, 167361401] ⟨2340047108783, 5, [(2, 1), (6991, 1), (167361401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6991
    · exact prime_167361401
  · decide +kernel

theorem prime_2342366254489 : Nat.Prime 2342366254489 := by
  apply nodeValid_prime [2, 3, 13, 17, 33970969] ⟨2342366254489, 11, [(2, 3), (3, 1), (13, 2), (17, 1), (33970969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_33970969
  · decide +kernel

theorem prime_2342366271727 : Nat.Prime 2342366271727 := by
  apply nodeValid_prime [2, 3, 13, 17, 19, 829, 8627] ⟨2342366271727, 3, [(2, 1), (3, 1), (13, 2), (17, 1), (19, 1), (829, 1), (8627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_19
    · exact prime_829
    · exact prime_8627
  · decide +kernel

theorem prime_2342366271977 : Nat.Prime 2342366271977 := by
  apply nodeValid_prime [2, 43, 6809204279] ⟨2342366271977, 3, [(2, 3), (43, 1), (6809204279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_6809204279
  · decide +kernel

theorem prime_2344686959539 : Nat.Prime 2344686959539 := by
  apply nodeValid_prime [2, 3, 7, 11, 41, 499, 7517] ⟨2344686959539, 13, [(2, 1), (3, 2), (7, 1), (11, 2), (41, 1), (499, 1), (7517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_41
    · exact prime_499
    · exact prime_7517
  · decide +kernel

theorem prime_2344686959963 : Nat.Prime 2344686959963 := by
  apply nodeValid_prime [2, 181, 6477035801] ⟨2344686959963, 2, [(2, 1), (181, 1), (6477035801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_6477035801
  · decide +kernel

theorem prime_2344686964219 : Nat.Prime 2344686964219 := by
  apply nodeValid_prime [2, 3, 101, 157, 2738231] ⟨2344686964219, 3, [(2, 1), (3, 3), (101, 1), (157, 1), (2738231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_157
    · exact prime_2738231
  · decide +kernel

theorem prime_2347009225963 : Nat.Prime 2347009225963 := by
  apply nodeValid_prime [2, 3, 127, 3080064601] ⟨2347009225963, 5, [(2, 1), (3, 1), (127, 1), (3080064601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_3080064601
  · decide +kernel

theorem prime_2347009245943 : Nat.Prime 2347009245943 := by
  apply nodeValid_prime [2, 3, 19, 20587800403] ⟨2347009245943, 5, [(2, 1), (3, 1), (19, 1), (20587800403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_20587800403
  · decide +kernel

theorem prime_2347009246031 : Nat.Prime 2347009246031 := by
  apply nodeValid_prime [2, 5, 234700924603] ⟨2347009246031, 7, [(2, 1), (5, 1), (234700924603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_234700924603
  · decide +kernel

theorem prime_2349333021533 : Nat.Prime 2349333021533 := by
  apply nodeValid_prime [2, 7, 457, 613, 42787] ⟨2349333021533, 5, [(2, 2), (7, 2), (457, 1), (613, 1), (42787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_457
    · exact prime_613
    · exact prime_42787
  · decide +kernel

theorem prime_2349333023413 : Nat.Prime 2349333023413 := by
  apply nodeValid_prime [2, 3, 577, 339302863] ⟨2349333023413, 2, [(2, 2), (3, 1), (577, 1), (339302863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
    · exact prime_339302863
  · decide +kernel

theorem prime_2349333040421 : Nat.Prime 2349333040421 := by
  apply nodeValid_prime [2, 5, 337, 348565733] ⟨2349333040421, 2, [(2, 2), (5, 1), (337, 1), (348565733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_337
    · exact prime_348565733
  · decide +kernel

theorem prime_2351658219571 : Nat.Prime 2351658219571 := by
  apply nodeValid_prime [2, 3, 5, 11, 383, 6202121] ⟨2351658219571, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (383, 1), (6202121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_383
    · exact prime_6202121
  · decide +kernel

theorem prime_2351658220633 : Nat.Prime 2351658220633 := by
  apply nodeValid_prime [2, 3, 7, 1555329511] ⟨2351658220633, 10, [(2, 3), (3, 3), (7, 1), (1555329511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1555329511
  · decide +kernel

theorem prime_2351658411607 : Nat.Prime 2351658411607 := by
  apply nodeValid_prime [2, 3, 7, 433, 129311471] ⟨2351658411607, 3, [(2, 1), (3, 1), (7, 1), (433, 1), (129311471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_433
    · exact prime_129311471
  · decide +kernel

theorem prime_2353985230447 : Nat.Prime 2353985230447 := by
  apply nodeValid_prime [2, 3, 17, 1423, 318001] ⟨2353985230447, 6, [(2, 1), (3, 2), (17, 2), (1423, 1), (318001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1423
    · exact prime_318001
  · decide +kernel

theorem prime_2353985231833 : Nat.Prime 2353985231833 := by
  apply nodeValid_prime [2, 3, 13, 93145981] ⟨2353985231833, 10, [(2, 3), (3, 5), (13, 1), (93145981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_93145981
  · decide +kernel

theorem prime_2353985336831 : Nat.Prime 2353985336831 := by
  apply nodeValid_prime [2, 5, 207811, 1132753] ⟨2353985336831, 13, [(2, 1), (5, 1), (207811, 1), (1132753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_207811
    · exact prime_1132753
  · decide +kernel

theorem prime_2356313776657 : Nat.Prime 2356313776657 := by
  apply nodeValid_prime [2, 3, 7, 23, 109, 2797303] ⟨2356313776657, 10, [(2, 4), (3, 1), (7, 1), (23, 1), (109, 1), (2797303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_109
    · exact prime_2797303
  · decide +kernel

theorem prime_2356313776717 : Nat.Prime 2356313776717 := by
  apply nodeValid_prime [2, 3, 17, 19, 223, 857, 3181] ⟨2356313776717, 5, [(2, 2), (3, 1), (17, 1), (19, 1), (223, 1), (857, 1), (3181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_223
    · exact prime_857
    · exact prime_3181
  · decide +kernel

theorem prime_2356313815943 : Nat.Prime 2356313815943 := by
  apply nodeValid_prime [2, 1303, 5101, 177257] ⟨2356313815943, 5, [(2, 1), (1303, 1), (5101, 1), (177257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1303
    · exact prime_5101
    · exact prime_177257
  · decide +kernel

theorem prime_2358643829371 : Nat.Prime 2358643829371 := by
  apply nodeValid_prime [2, 3, 5, 233, 12347, 27329] ⟨2358643829371, 2, [(2, 1), (3, 1), (5, 1), (233, 1), (12347, 1), (27329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233
    · exact prime_12347
    · exact prime_27329
  · decide +kernel

theorem prime_2358643830617 : Nat.Prime 2358643830617 := by
  apply nodeValid_prime [2, 294830478827] ⟨2358643830617, 3, [(2, 3), (294830478827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_294830478827
  · decide +kernel

theorem prime_2358643850177 : Nat.Prime 2358643850177 := by
  apply nodeValid_prime [2, 9181, 4014139] ⟨2358643850177, 3, [(2, 6), (9181, 1), (4014139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9181
    · exact prime_4014139
  · decide +kernel

end Sude.Lucas.Generated
