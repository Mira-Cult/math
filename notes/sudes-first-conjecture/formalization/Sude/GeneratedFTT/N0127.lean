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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0107

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_14177 : Nat.Prime 14177 := by
  apply nodeValid_prime [2, 443] ⟨14177, 3, [(2, 5), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_443
  · decide +kernel

theorem prime_16763 : Nat.Prime 16763 := by
  apply nodeValid_prime [2, 17, 29] ⟨16763, 2, [(2, 1), (17, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_17209 : Nat.Prime 17209 := by
  apply nodeValid_prime [2, 3, 239] ⟨17209, 14, [(2, 3), (3, 2), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
  · decide +kernel

theorem prime_17359 : Nat.Prime 17359 := by
  apply nodeValid_prime [2, 3, 11, 263] ⟨17359, 3, [(2, 1), (3, 1), (11, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_263
  · decide +kernel

theorem prime_22921 : Nat.Prime 22921 := by
  apply nodeValid_prime [2, 3, 5, 191] ⟨22921, 7, [(2, 3), (3, 1), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_23663 : Nat.Prime 23663 := by
  apply nodeValid_prime [2, 11831] ⟨23663, 5, [(2, 1), (11831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11831
  · decide +kernel

theorem prime_23767 : Nat.Prime 23767 := by
  apply nodeValid_prime [2, 3, 17, 233] ⟨23767, 3, [(2, 1), (3, 1), (17, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_233
  · decide +kernel

theorem prime_27479 : Nat.Prime 27479 := by
  apply nodeValid_prime [2, 11, 1249] ⟨27479, 7, [(2, 1), (11, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1249
  · decide +kernel

theorem prime_36277 : Nat.Prime 36277 := by
  apply nodeValid_prime [2, 3, 3023] ⟨36277, 2, [(2, 2), (3, 1), (3023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3023
  · decide +kernel

theorem prime_44383 : Nat.Prime 44383 := by
  apply nodeValid_prime [2, 3, 13, 569] ⟨44383, 3, [(2, 1), (3, 1), (13, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_569
  · decide +kernel

theorem prime_44843 : Nat.Prime 44843 := by
  apply nodeValid_prime [2, 7, 3203] ⟨44843, 5, [(2, 1), (7, 1), (3203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3203
  · decide +kernel

theorem prime_46861 : Nat.Prime 46861 := by
  apply nodeValid_prime [2, 3, 5, 11, 71] ⟨46861, 6, [(2, 2), (3, 1), (5, 1), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_51599 : Nat.Prime 51599 := by
  apply nodeValid_prime [2, 25799] ⟨51599, 7, [(2, 1), (25799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25799
  · decide +kernel

theorem prime_54773 : Nat.Prime 54773 := by
  apply nodeValid_prime [2, 13693] ⟨54773, 2, [(2, 2), (13693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13693
  · decide +kernel

theorem prime_54959 : Nat.Prime 54959 := by
  apply nodeValid_prime [2, 27479] ⟨54959, 7, [(2, 1), (27479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27479
  · decide +kernel

theorem prime_62473 : Nat.Prime 62473 := by
  apply nodeValid_prime [2, 3, 19, 137] ⟨62473, 5, [(2, 3), (3, 1), (19, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_65677 : Nat.Prime 65677 := by
  apply nodeValid_prime [2, 3, 13, 421] ⟨65677, 2, [(2, 2), (3, 1), (13, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_421
  · decide +kernel

theorem prime_68791 : Nat.Prime 68791 := by
  apply nodeValid_prime [2, 3, 5, 2293] ⟨68791, 3, [(2, 1), (3, 1), (5, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2293
  · decide +kernel

theorem prime_71899 : Nat.Prime 71899 := by
  apply nodeValid_prime [2, 3, 23, 521] ⟨71899, 2, [(2, 1), (3, 1), (23, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_521
  · decide +kernel

theorem prime_73009 : Nat.Prime 73009 := by
  apply nodeValid_prime [2, 3, 13] ⟨73009, 7, [(2, 4), (3, 3), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_73771 : Nat.Prime 73771 := by
  apply nodeValid_prime [2, 3, 5, 2459] ⟨73771, 2, [(2, 1), (3, 1), (5, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2459
  · decide +kernel

theorem prime_75377 : Nat.Prime 75377 := by
  apply nodeValid_prime [2, 7, 673] ⟨75377, 3, [(2, 4), (7, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_673
  · decide +kernel

theorem prime_77249 : Nat.Prime 77249 := by
  apply nodeValid_prime [2, 17, 71] ⟨77249, 3, [(2, 6), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_83857 : Nat.Prime 83857 := by
  apply nodeValid_prime [2, 3, 1747] ⟨83857, 5, [(2, 4), (3, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1747
  · decide +kernel

theorem prime_95617 : Nat.Prime 95617 := by
  apply nodeValid_prime [2, 3, 83] ⟨95617, 5, [(2, 7), (3, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_102607 : Nat.Prime 102607 := by
  apply nodeValid_prime [2, 3, 7, 349] ⟨102607, 5, [(2, 1), (3, 1), (7, 2), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_349
  · decide +kernel

theorem prime_109919 : Nat.Prime 109919 := by
  apply nodeValid_prime [2, 54959] ⟨109919, 17, [(2, 1), (54959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54959
  · decide +kernel

theorem prime_122081 : Nat.Prime 122081 := by
  apply nodeValid_prime [2, 5, 7, 109] ⟨122081, 3, [(2, 5), (5, 1), (7, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_109
  · decide +kernel

theorem prime_136991 : Nat.Prime 136991 := by
  apply nodeValid_prime [2, 5, 7, 19, 103] ⟨136991, 19, [(2, 1), (5, 1), (7, 1), (19, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_103
  · decide +kernel

theorem prime_145109 : Nat.Prime 145109 := by
  apply nodeValid_prime [2, 36277] ⟨145109, 2, [(2, 2), (36277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36277
  · decide +kernel

theorem prime_165173 : Nat.Prime 165173 := by
  apply nodeValid_prime [2, 7, 17, 347] ⟨165173, 2, [(2, 2), (7, 1), (17, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_347
  · decide +kernel

theorem prime_166027 : Nat.Prime 166027 := by
  apply nodeValid_prime [2, 3, 7, 59, 67] ⟨166027, 2, [(2, 1), (3, 1), (7, 1), (59, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_67
  · decide +kernel

theorem prime_179437 : Nat.Prime 179437 := by
  apply nodeValid_prime [2, 3, 19, 787] ⟨179437, 6, [(2, 2), (3, 1), (19, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_787
  · decide +kernel

theorem prime_186743 : Nat.Prime 186743 := by
  apply nodeValid_prime [2, 93371] ⟨186743, 5, [(2, 1), (93371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93371
  · decide +kernel

theorem prime_221281 : Nat.Prime 221281 := by
  apply nodeValid_prime [2, 3, 5, 461] ⟨221281, 13, [(2, 5), (3, 1), (5, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_461
  · decide +kernel

theorem prime_260317 : Nat.Prime 260317 := by
  apply nodeValid_prime [2, 3, 7, 1033] ⟨260317, 18, [(2, 2), (3, 2), (7, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1033
  · decide +kernel

theorem prime_318793 : Nat.Prime 318793 := by
  apply nodeValid_prime [2, 3, 37, 359] ⟨318793, 7, [(2, 3), (3, 1), (37, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_359
  · decide +kernel

theorem prime_321947 : Nat.Prime 321947 := by
  apply nodeValid_prime [2, 17, 557] ⟨321947, 2, [(2, 1), (17, 2), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_557
  · decide +kernel

theorem prime_394063 : Nat.Prime 394063 := by
  apply nodeValid_prime [2, 3, 65677] ⟨394063, 5, [(2, 1), (3, 1), (65677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_65677
  · decide +kernel

theorem prime_411011 : Nat.Prime 411011 := by
  apply nodeValid_prime [2, 5, 23, 1787] ⟨411011, 2, [(2, 1), (5, 1), (23, 1), (1787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1787
  · decide +kernel

theorem prime_473923 : Nat.Prime 473923 := by
  apply nodeValid_prime [2, 3, 113, 233] ⟨473923, 2, [(2, 1), (3, 2), (113, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_233
  · decide +kernel

theorem prime_514681 : Nat.Prime 514681 := by
  apply nodeValid_prime [2, 3, 5, 4289] ⟨514681, 13, [(2, 3), (3, 1), (5, 1), (4289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4289
  · decide +kernel

theorem prime_518989 : Nat.Prime 518989 := by
  apply nodeValid_prime [2, 3, 61, 709] ⟨518989, 2, [(2, 2), (3, 1), (61, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_709
  · decide +kernel

theorem prime_536273 : Nat.Prime 536273 := by
  apply nodeValid_prime [2, 11, 277] ⟨536273, 5, [(2, 4), (11, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_277
  · decide +kernel

theorem prime_545329 : Nat.Prime 545329 := by
  apply nodeValid_prime [2, 3, 7, 541] ⟨545329, 17, [(2, 4), (3, 2), (7, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_541
  · decide +kernel

theorem prime_619189 : Nat.Prime 619189 := by
  apply nodeValid_prime [2, 3, 51599] ⟨619189, 2, [(2, 2), (3, 1), (51599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51599
  · decide +kernel

theorem prime_624731 : Nat.Prime 624731 := by
  apply nodeValid_prime [2, 5, 62473] ⟨624731, 2, [(2, 1), (5, 1), (62473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_62473
  · decide +kernel

theorem prime_625483 : Nat.Prime 625483 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨625483, 3, [(2, 1), (3, 7), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_633953 : Nat.Prime 633953 := by
  apply nodeValid_prime [2, 11, 1801] ⟨633953, 3, [(2, 5), (11, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1801
  · decide +kernel

theorem prime_782687 : Nat.Prime 782687 := by
  apply nodeValid_prime [2, 19, 43, 479] ⟨782687, 5, [(2, 1), (19, 1), (43, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_479
  · decide +kernel

theorem prime_852671 : Nat.Prime 852671 := by
  apply nodeValid_prime [2, 5, 7, 13, 937] ⟨852671, 14, [(2, 1), (5, 1), (7, 1), (13, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_937
  · decide +kernel

theorem prime_856279 : Nat.Prime 856279 := by
  apply nodeValid_prime [2, 3, 101, 157] ⟨856279, 3, [(2, 1), (3, 3), (101, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_157
  · decide +kernel

theorem prime_1041269 : Nat.Prime 1041269 := by
  apply nodeValid_prime [2, 260317] ⟨1041269, 2, [(2, 2), (260317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_260317
  · decide +kernel

theorem prime_1081981 : Nat.Prime 1081981 := by
  apply nodeValid_prime [2, 3, 5, 6011] ⟨1081981, 6, [(2, 2), (3, 2), (5, 1), (6011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6011
  · decide +kernel

theorem prime_1161851 : Nat.Prime 1161851 := by
  apply nodeValid_prime [2, 5, 19, 1223] ⟨1161851, 2, [(2, 1), (5, 2), (19, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1223
  · decide +kernel

theorem prime_1267907 : Nat.Prime 1267907 := by
  apply nodeValid_prime [2, 633953] ⟨1267907, 2, [(2, 1), (633953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_633953
  · decide +kernel

theorem prime_1545329 : Nat.Prime 1545329 := by
  apply nodeValid_prime [2, 59, 1637] ⟨1545329, 3, [(2, 4), (59, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_1637
  · decide +kernel

theorem prime_2147881 : Nat.Prime 2147881 := by
  apply nodeValid_prime [2, 3, 5, 7, 2557] ⟨2147881, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (2557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2557
  · decide +kernel

theorem prime_2872997 : Nat.Prime 2872997 := by
  apply nodeValid_prime [2, 7, 102607] ⟨2872997, 2, [(2, 2), (7, 1), (102607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_102607
  · decide +kernel

theorem prime_3686251 : Nat.Prime 3686251 := by
  apply nodeValid_prime [2, 3, 5, 983] ⟨3686251, 2, [(2, 1), (3, 1), (5, 4), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_983
  · decide +kernel

theorem prime_5151541 : Nat.Prime 5151541 := by
  apply nodeValid_prime [2, 3, 5, 23, 3733] ⟨5151541, 7, [(2, 2), (3, 1), (5, 1), (23, 1), (3733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_3733
  · decide +kernel

theorem prime_6100859 : Nat.Prime 6100859 := by
  apply nodeValid_prime [2, 17, 179437] ⟨6100859, 2, [(2, 1), (17, 1), (179437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_179437
  · decide +kernel

theorem prime_7607443 : Nat.Prime 7607443 := by
  apply nodeValid_prime [2, 3, 1267907] ⟨7607443, 5, [(2, 1), (3, 1), (1267907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1267907
  · decide +kernel

theorem prime_10725461 : Nat.Prime 10725461 := by
  apply nodeValid_prime [2, 5, 536273] ⟨10725461, 2, [(2, 2), (5, 1), (536273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_536273
  · decide +kernel

theorem prime_12982003 : Nat.Prime 12982003 := by
  apply nodeValid_prime [2, 3, 11, 239, 823] ⟨12982003, 2, [(2, 1), (3, 1), (11, 1), (239, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_239
    · exact prime_823
  · decide +kernel

theorem prime_13338529 : Nat.Prime 13338529 := by
  apply nodeValid_prime [2, 3, 7, 23, 863] ⟨13338529, 11, [(2, 5), (3, 1), (7, 1), (23, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_863
  · decide +kernel

theorem prime_13590517 : Nat.Prime 13590517 := by
  apply nodeValid_prime [2, 3, 23, 41, 1201] ⟨13590517, 2, [(2, 2), (3, 1), (23, 1), (41, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_1201
  · decide +kernel

theorem prime_15579241 : Nat.Prime 15579241 := by
  apply nodeValid_prime [2, 3, 5, 19, 6833] ⟨15579241, 11, [(2, 3), (3, 1), (5, 1), (19, 1), (6833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_6833
  · decide +kernel

theorem prime_16110821 : Nat.Prime 16110821 := by
  apply nodeValid_prime [2, 5, 11, 67, 1093] ⟨16110821, 3, [(2, 2), (5, 1), (11, 1), (67, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_67
    · exact prime_1093
  · decide +kernel

theorem prime_17565473 : Nat.Prime 17565473 := by
  apply nodeValid_prime [2, 53, 10357] ⟨17565473, 3, [(2, 5), (53, 1), (10357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_10357
  · decide +kernel

theorem prime_19039049 : Nat.Prime 19039049 := by
  apply nodeValid_prime [2, 7, 17, 2857] ⟨19039049, 6, [(2, 3), (7, 2), (17, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_2857
  · decide +kernel

theorem prime_25485997 : Nat.Prime 25485997 := by
  apply nodeValid_prime [2, 3, 67, 31699] ⟨25485997, 2, [(2, 2), (3, 1), (67, 1), (31699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_31699
  · decide +kernel

theorem prime_25620769 : Nat.Prime 25620769 := by
  apply nodeValid_prime [2, 3, 17, 5233] ⟨25620769, 7, [(2, 5), (3, 2), (17, 1), (5233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_5233
  · decide +kernel

theorem prime_28839757 : Nat.Prime 28839757 := by
  apply nodeValid_prime [2, 3, 11, 43, 5081] ⟨28839757, 5, [(2, 2), (3, 1), (11, 1), (43, 1), (5081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_5081
  · decide +kernel

theorem prime_40221959 : Nat.Prime 40221959 := by
  apply nodeValid_prime [2, 7, 2872997] ⟨40221959, 7, [(2, 1), (7, 1), (2872997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2872997
  · decide +kernel

theorem prime_45644659 : Nat.Prime 45644659 := by
  apply nodeValid_prime [2, 3, 7607443] ⟨45644659, 3, [(2, 1), (3, 1), (7607443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7607443
  · decide +kernel

theorem prime_53087627 : Nat.Prime 53087627 := by
  apply nodeValid_prime [2, 113, 467, 503] ⟨53087627, 2, [(2, 1), (113, 1), (467, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_467
    · exact prime_503
  · decide +kernel

theorem prime_61381451 : Nat.Prime 61381451 := by
  apply nodeValid_prime [2, 5, 13, 94433] ⟨61381451, 6, [(2, 1), (5, 2), (13, 1), (94433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_94433
  · decide +kernel

theorem prime_81920711 : Nat.Prime 81920711 := by
  apply nodeValid_prime [2, 5, 23, 353, 1009] ⟨81920711, 11, [(2, 1), (5, 1), (23, 1), (353, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_353
    · exact prime_1009
  · decide +kernel

theorem prime_84527857 : Nat.Prime 84527857 := by
  apply nodeValid_prime [2, 3, 7, 83857] ⟨84527857, 10, [(2, 4), (3, 2), (7, 1), (83857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83857
  · decide +kernel

theorem prime_110587531 : Nat.Prime 110587531 := by
  apply nodeValid_prime [2, 3, 5, 3686251] ⟨110587531, 2, [(2, 1), (3, 1), (5, 1), (3686251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3686251
  · decide +kernel

theorem prime_162261289 : Nat.Prime 162261289 := by
  apply nodeValid_prime [2, 3, 7, 321947] ⟨162261289, 13, [(2, 3), (3, 2), (7, 1), (321947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_321947
  · decide +kernel

theorem prime_328118491 : Nat.Prime 328118491 := by
  apply nodeValid_prime [2, 3, 5, 7, 41, 12703] ⟨328118491, 12, [(2, 1), (3, 2), (5, 1), (7, 1), (41, 1), (12703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_12703
  · decide +kernel

theorem prime_489536251 : Nat.Prime 489536251 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 1097] ⟨489536251, 3, [(2, 1), (3, 1), (5, 4), (7, 1), (17, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_1097
  · decide +kernel

theorem prime_568250497 : Nat.Prime 568250497 := by
  apply nodeValid_prime [2, 3, 11, 44843] ⟨568250497, 5, [(2, 7), (3, 2), (11, 1), (44843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_44843
  · decide +kernel

theorem prime_704255641 : Nat.Prime 704255641 := by
  apply nodeValid_prime [2, 3, 5, 11, 127, 4201] ⟨704255641, 23, [(2, 3), (3, 1), (5, 1), (11, 1), (127, 1), (4201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_127
    · exact prime_4201
  · decide +kernel

theorem prime_736807153 : Nat.Prime 736807153 := by
  apply nodeValid_prime [2, 3, 1637, 9377] ⟨736807153, 5, [(2, 4), (3, 1), (1637, 1), (9377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1637
    · exact prime_9377
  · decide +kernel

theorem prime_845278571 : Nat.Prime 845278571 := by
  apply nodeValid_prime [2, 5, 84527857] ⟨845278571, 2, [(2, 1), (5, 1), (84527857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_84527857
  · decide +kernel

theorem prime_1089467839 : Nat.Prime 1089467839 := by
  apply nodeValid_prime [2, 3, 67, 223, 4051] ⟨1089467839, 6, [(2, 1), (3, 2), (67, 1), (223, 1), (4051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_223
    · exact prime_4051
  · decide +kernel

theorem prime_1152075733 : Nat.Prime 1152075733 := by
  apply nodeValid_prime [2, 3, 1933, 49667] ⟨1152075733, 2, [(2, 2), (3, 1), (1933, 1), (49667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1933
    · exact prime_49667
  · decide +kernel

theorem prime_2286272411 : Nat.Prime 2286272411 := by
  apply nodeValid_prime [2, 5, 14753, 15497] ⟨2286272411, 2, [(2, 1), (5, 1), (14753, 1), (15497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14753
    · exact prime_15497
  · decide +kernel

theorem prime_2551983107 : Nat.Prime 2551983107 := by
  apply nodeValid_prime [2, 17747, 71899] ⟨2551983107, 2, [(2, 1), (17747, 1), (71899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17747
    · exact prime_71899
  · decide +kernel

theorem prime_2920767667 : Nat.Prime 2920767667 := by
  apply nodeValid_prime [2, 3, 19, 25620769] ⟨2920767667, 11, [(2, 1), (3, 1), (19, 1), (25620769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_25620769
  · decide +kernel

theorem prime_3055148189 : Nat.Prime 3055148189 := by
  apply nodeValid_prime [2, 17209, 44383] ⟨3055148189, 2, [(2, 2), (17209, 1), (44383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17209
    · exact prime_44383
  · decide +kernel

theorem prime_4481305313 : Nat.Prime 4481305313 := by
  apply nodeValid_prime [2, 11, 73, 2389] ⟨4481305313, 3, [(2, 5), (11, 1), (73, 2), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
    · exact prime_2389
  · decide +kernel

theorem prime_4487042057 : Nat.Prime 4487042057 := by
  apply nodeValid_prime [2, 7, 1063, 75377] ⟨4487042057, 3, [(2, 3), (7, 1), (1063, 1), (75377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1063
    · exact prime_75377
  · decide +kernel

theorem prime_7163921731 : Nat.Prime 7163921731 := by
  apply nodeValid_prime [2, 3, 5, 7, 83, 411011] ⟨7163921731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (83, 1), (411011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_83
    · exact prime_411011
  · decide +kernel

theorem prime_7570099297 : Nat.Prime 7570099297 := by
  apply nodeValid_prime [2, 3, 23, 4703] ⟨7570099297, 7, [(2, 5), (3, 7), (23, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_4703
  · decide +kernel

theorem prime_9046105997 : Nat.Prime 9046105997 := by
  apply nodeValid_prime [2, 439, 5151541] ⟨9046105997, 2, [(2, 2), (439, 1), (5151541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_439
    · exact prime_5151541
  · decide +kernel

theorem prime_10817597513 : Nat.Prime 10817597513 := by
  apply nodeValid_prime [2, 18521, 73009] ⟨10817597513, 3, [(2, 3), (18521, 1), (73009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18521
    · exact prime_73009
  · decide +kernel

theorem prime_17526827107 : Nat.Prime 17526827107 := by
  apply nodeValid_prime [2, 3, 73, 13338529] ⟨17526827107, 2, [(2, 1), (3, 2), (73, 1), (13338529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_13338529
  · decide +kernel

theorem prime_21629822651 : Nat.Prime 21629822651 := by
  apply nodeValid_prime [2, 5, 41, 131, 239, 337] ⟨21629822651, 2, [(2, 1), (5, 2), (41, 1), (131, 1), (239, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_131
    · exact prime_239
    · exact prime_337
  · decide +kernel

theorem prime_21992354903 : Nat.Prime 21992354903 := by
  apply nodeValid_prime [2, 7, 43, 59, 619189] ⟨21992354903, 5, [(2, 1), (7, 1), (43, 1), (59, 1), (619189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_59
    · exact prime_619189
  · decide +kernel

theorem prime_22216683823 : Nat.Prime 22216683823 := by
  apply nodeValid_prime [2, 3, 5927, 624731] ⟨22216683823, 5, [(2, 1), (3, 1), (5927, 1), (624731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5927
    · exact prime_624731
  · decide +kernel

theorem prime_27362158469 : Nat.Prime 27362158469 := by
  apply nodeValid_prime [2, 17359, 394063] ⟨27362158469, 2, [(2, 2), (17359, 1), (394063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17359
    · exact prime_394063
  · decide +kernel

theorem prime_28107020849 : Nat.Prime 28107020849 := by
  apply nodeValid_prime [2, 181, 661, 14683] ⟨28107020849, 3, [(2, 4), (181, 1), (661, 1), (14683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_661
    · exact prime_14683
  · decide +kernel

theorem prime_42795302839 : Nat.Prime 42795302839 := by
  apply nodeValid_prime [2, 3, 32233, 221281] ⟨42795302839, 3, [(2, 1), (3, 1), (32233, 1), (221281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32233
    · exact prime_221281
  · decide +kernel

theorem prime_48854031007 : Nat.Prime 48854031007 := by
  apply nodeValid_prime [2, 3, 11, 479, 1545329] ⟨48854031007, 3, [(2, 1), (3, 1), (11, 1), (479, 1), (1545329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_479
    · exact prime_1545329
  · decide +kernel

theorem prime_75487272233 : Nat.Prime 75487272233 := by
  apply nodeValid_prime [2, 19, 9067, 54773] ⟨75487272233, 3, [(2, 3), (19, 1), (9067, 1), (54773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_9067
    · exact prime_54773
  · decide +kernel

theorem prime_108715224301 : Nat.Prime 108715224301 := by
  apply nodeValid_prime [2, 3, 5, 463, 782687] ⟨108715224301, 6, [(2, 2), (3, 1), (5, 2), (463, 1), (782687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_463
    · exact prime_782687
  · decide +kernel

theorem prime_133300102939 : Nat.Prime 133300102939 := by
  apply nodeValid_prime [2, 3, 22216683823] ⟨133300102939, 2, [(2, 1), (3, 1), (22216683823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22216683823
  · decide +kernel

theorem prime_235198755923 : Nat.Prime 235198755923 := by
  apply nodeValid_prime [2, 13, 9046105997] ⟨235198755923, 2, [(2, 1), (13, 1), (9046105997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_9046105997
  · decide +kernel

theorem prime_235900897597 : Nat.Prime 235900897597 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 53, 229, 349] ⟨235900897597, 6, [(2, 2), (3, 2), (7, 1), (13, 1), (17, 1), (53, 1), (229, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_53
    · exact prime_229
    · exact prime_349
  · decide +kernel

theorem prime_253532030761 : Nat.Prime 253532030761 := by
  apply nodeValid_prime [2, 3, 5, 704255641] ⟨253532030761, 17, [(2, 3), (3, 2), (5, 1), (704255641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_704255641
  · decide +kernel

theorem prime_468646155391 : Nat.Prime 468646155391 := by
  apply nodeValid_prime [2, 3, 5, 7, 1039, 2147881] ⟨468646155391, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (1039, 1), (2147881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1039
    · exact prime_2147881
  · decide +kernel

theorem prime_935194926971 : Nat.Prime 935194926971 := by
  apply nodeValid_prime [2, 5, 19, 29, 163, 1041269] ⟨935194926971, 2, [(2, 1), (5, 1), (19, 1), (29, 1), (163, 1), (1041269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_163
    · exact prime_1041269
  · decide +kernel

theorem prime_937992140951 : Nat.Prime 937992140951 := by
  apply nodeValid_prime [2, 5, 229, 81920711] ⟨937992140951, 19, [(2, 1), (5, 2), (229, 1), (81920711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_81920711
  · decide +kernel

theorem prime_1411192535539 : Nat.Prime 1411192535539 := by
  apply nodeValid_prime [2, 3, 235198755923] ⟨1411192535539, 2, [(2, 1), (3, 1), (235198755923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_235198755923
  · decide +kernel

theorem prime_5565190128103 : Nat.Prime 5565190128103 := by
  apply nodeValid_prime [2, 3, 11, 28107020849] ⟨5565190128103, 3, [(2, 1), (3, 2), (11, 1), (28107020849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_28107020849
  · decide +kernel

theorem prime_5565190128889 : Nat.Prime 5565190128889 := by
  apply nodeValid_prime [2, 3, 13, 37, 563, 856279] ⟨5565190128889, 7, [(2, 3), (3, 1), (13, 1), (37, 1), (563, 1), (856279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_563
    · exact prime_856279
  · decide +kernel

theorem prime_5565190178897 : Nat.Prime 5565190178897 := by
  apply nodeValid_prime [2, 18269, 19039049] ⟨5565190178897, 3, [(2, 4), (18269, 1), (19039049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18269
    · exact prime_19039049
  · decide +kernel

theorem prime_5569359534799 : Nat.Prime 5569359534799 := by
  apply nodeValid_prime [2, 3, 19, 48854031007] ⟨5569359534799, 7, [(2, 1), (3, 1), (19, 1), (48854031007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_48854031007
  · decide +kernel

theorem prime_5569359592969 : Nat.Prime 5569359592969 := by
  apply nodeValid_prime [2, 3, 71, 1089467839] ⟨5569359592969, 11, [(2, 3), (3, 2), (71, 1), (1089467839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_1089467839
  · decide +kernel

theorem prime_5569359593197 : Nat.Prime 5569359593197 := by
  apply nodeValid_prime [2, 3, 7, 29, 2286272411] ⟨5569359593197, 14, [(2, 2), (3, 1), (7, 1), (29, 1), (2286272411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_2286272411
  · decide +kernel

theorem prime_5573531020027 : Nat.Prime 5573531020027 := by
  apply nodeValid_prime [2, 3, 53, 17526827107] ⟨5573531020027, 5, [(2, 1), (3, 1), (53, 1), (17526827107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_17526827107
  · decide +kernel

theorem prime_5573531105689 : Nat.Prime 5573531105689 := by
  apply nodeValid_prime [2, 3, 7, 13, 2551983107] ⟨5573531105689, 19, [(2, 3), (3, 1), (7, 1), (13, 1), (2551983107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_2551983107
  · decide +kernel

theorem prime_5573531106719 : Nat.Prime 5573531106719 := by
  apply nodeValid_prime [2, 389, 7163921731] ⟨5573531106719, 7, [(2, 1), (389, 1), (7163921731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_389
    · exact prime_7163921731
  · decide +kernel

theorem prime_5577704618383 : Nat.Prime 5577704618383 := by
  apply nodeValid_prime [2, 3, 13, 449, 53087627] ⟨5577704618383, 5, [(2, 1), (3, 2), (13, 1), (449, 1), (53087627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_449
    · exact prime_53087627
  · decide +kernel

theorem prime_5577704675707 : Nat.Prime 5577704675707 := by
  apply nodeValid_prime [2, 3, 67, 95617, 145109] ⟨5577704675707, 2, [(2, 1), (3, 1), (67, 1), (95617, 1), (145109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_95617
    · exact prime_145109
  · decide +kernel

theorem prime_5577704676743 : Nat.Prime 5577704676743 := by
  apply nodeValid_prime [2, 11, 253532030761] ⟨5577704676743, 5, [(2, 1), (11, 1), (253532030761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_253532030761
  · decide +kernel

theorem prime_5581880316709 : Nat.Prime 5581880316709 := by
  apply nodeValid_prime [2, 3, 43, 10817597513] ⟨5581880316709, 2, [(2, 2), (3, 1), (43, 1), (10817597513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_10817597513
  · decide +kernel

theorem prime_5581880318909 : Nat.Prime 5581880318909 := by
  apply nodeValid_prime [2, 311, 4487042057] ⟨5581880318909, 2, [(2, 2), (311, 1), (4487042057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_4487042057
  · decide +kernel

theorem prime_5581880327677 : Nat.Prime 5581880327677 := by
  apply nodeValid_prime [2, 3, 17, 27362158469] ⟨5581880327677, 2, [(2, 2), (3, 1), (17, 1), (27362158469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_27362158469
  · decide +kernel

theorem prime_5586058145243 : Nat.Prime 5586058145243 := by
  apply nodeValid_prime [2, 37, 75487272233] ⟨5586058145243, 2, [(2, 1), (37, 1), (75487272233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_75487272233
  · decide +kernel

theorem prime_5586058145363 : Nat.Prime 5586058145363 := by
  apply nodeValid_prime [2, 127, 21992354903] ⟨5586058145363, 2, [(2, 1), (127, 1), (21992354903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_21992354903
  · decide +kernel

theorem prime_5586058153601 : Nat.Prime 5586058153601 := by
  apply nodeValid_prime [2, 5, 23663, 73771] ⟨5586058153601, 3, [(2, 7), (5, 2), (23663, 1), (73771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23663
    · exact prime_73771
  · decide +kernel

theorem prime_5590238007349 : Nat.Prime 5590238007349 := by
  apply nodeValid_prime [2, 3, 17, 9551, 318793] ⟨5590238007349, 6, [(2, 2), (3, 3), (17, 1), (9551, 1), (318793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9551
    · exact prime_318793
  · decide +kernel

theorem prime_5590238008441 : Nat.Prime 5590238008441 := by
  apply nodeValid_prime [2, 3, 5, 43, 61, 379, 46861] ⟨5590238008441, 26, [(2, 3), (3, 1), (5, 1), (43, 1), (61, 1), (379, 1), (46861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_61
    · exact prime_379
    · exact prime_46861
  · decide +kernel

theorem prime_5590238096627 : Nat.Prime 5590238096627 := by
  apply nodeValid_prime [2, 191, 857, 3449, 4951] ⟨5590238096627, 2, [(2, 1), (191, 1), (857, 1), (3449, 1), (4951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_857
    · exact prime_3449
    · exact prime_4951
  · decide +kernel

theorem prime_5594420155283 : Nat.Prime 5594420155283 := by
  apply nodeValid_prime [2, 7, 17, 59, 16763, 23767] ⟨5594420155283, 5, [(2, 1), (7, 1), (17, 1), (59, 1), (16763, 1), (23767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_59
    · exact prime_16763
    · exact prime_23767
  · decide +kernel

theorem prime_5594420271551 : Nat.Prime 5594420271551 := by
  apply nodeValid_prime [2, 5, 11, 31, 328118491] ⟨5594420271551, 11, [(2, 1), (5, 2), (11, 1), (31, 1), (328118491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_328118491
  · decide +kernel

theorem prime_5594420276429 : Nat.Prime 5594420276429 := by
  apply nodeValid_prime [2, 2857, 489536251] ⟨5594420276429, 2, [(2, 2), (2857, 1), (489536251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2857
    · exact prime_489536251
  · decide +kernel

theorem prime_5598604323439 : Nat.Prime 5598604323439 := by
  apply nodeValid_prime [2, 3, 7, 133300102939] ⟨5598604323439, 3, [(2, 1), (3, 1), (7, 1), (133300102939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_133300102939
  · decide +kernel

theorem prime_5598604344407 : Nat.Prime 5598604344407 := by
  apply nodeValid_prime [2, 17, 1489, 110587531] ⟨5598604344407, 5, [(2, 1), (17, 1), (1489, 1), (110587531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1489
    · exact prime_110587531
  · decide +kernel

theorem prime_5598604346897 : Nat.Prime 5598604346897 := by
  apply nodeValid_prime [2, 11, 1103, 28839757] ⟨5598604346897, 3, [(2, 4), (11, 1), (1103, 1), (28839757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1103
    · exact prime_28839757
  · decide +kernel

theorem prime_5602790602589 : Nat.Prime 5602790602589 := by
  apply nodeValid_prime [2, 83, 32789, 514681] ⟨5602790602589, 2, [(2, 2), (83, 1), (32789, 1), (514681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_32789
    · exact prime_514681
  · decide +kernel

theorem prime_5602790602933 : Nat.Prime 5602790602933 := by
  apply nodeValid_prime [2, 3, 53, 193, 45644659] ⟨5602790602933, 2, [(2, 2), (3, 1), (53, 1), (193, 1), (45644659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_193
    · exact prime_45644659
  · decide +kernel

theorem prime_5602790608487 : Nat.Prime 5602790608487 := by
  apply nodeValid_prime [2, 109919, 25485997] ⟨5602790608487, 5, [(2, 1), (109919, 1), (25485997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109919
    · exact prime_25485997
  · decide +kernel

theorem prime_5606979023713 : Nat.Prime 5606979023713 := by
  apply nodeValid_prime [2, 3, 11, 409, 12982003] ⟨5606979023713, 5, [(2, 5), (3, 1), (11, 1), (409, 1), (12982003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_409
    · exact prime_12982003
  · decide +kernel

theorem prime_5606979115561 : Nat.Prime 5606979115561 := by
  apply nodeValid_prime [2, 3, 5, 401, 8219, 14177] ⟨5606979115561, 13, [(2, 3), (3, 1), (5, 1), (401, 1), (8219, 1), (14177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_401
    · exact prime_8219
    · exact prime_14177
  · decide +kernel

theorem prime_5606979116731 : Nat.Prime 5606979116731 := by
  apply nodeValid_prime [2, 3, 5, 397, 2521, 186743] ⟨5606979116731, 10, [(2, 1), (3, 1), (5, 1), (397, 1), (2521, 1), (186743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_397
    · exact prime_2521
    · exact prime_186743
  · decide +kernel

theorem prime_5611169561827 : Nat.Prime 5611169561827 := by
  apply nodeValid_prime [2, 3, 935194926971] ⟨5611169561827, 2, [(2, 1), (3, 1), (935194926971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_935194926971
  · decide +kernel

theorem prime_5611169603089 : Nat.Prime 5611169603089 := by
  apply nodeValid_prime [2, 3, 7, 19, 4259, 68791] ⟨5611169603089, 11, [(2, 4), (3, 2), (7, 1), (19, 1), (4259, 1), (68791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_4259
    · exact prime_68791
  · decide +kernel

theorem prime_5615362216267 : Nat.Prime 5615362216267 := by
  apply nodeValid_prime [2, 3, 11, 5281, 16110821] ⟨5615362216267, 13, [(2, 1), (3, 1), (11, 1), (5281, 1), (16110821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5281
    · exact prime_16110821
  · decide +kernel

theorem prime_5615362371383 : Nat.Prime 5615362371383 := by
  apply nodeValid_prime [2, 919, 3055148189] ⟨5615362371383, 5, [(2, 1), (919, 1), (3055148189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_919
    · exact prime_3055148189
  · decide +kernel

theorem prime_5615362372091 : Nat.Prime 5615362372091 := by
  apply nodeValid_prime [2, 5, 518989, 1081981] ⟨5615362372091, 6, [(2, 1), (5, 1), (518989, 1), (1081981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_518989
    · exact prime_1081981
  · decide +kernel

theorem prime_5619556862503 : Nat.Prime 5619556862503 := by
  apply nodeValid_prime [2, 3, 11, 19, 4481305313] ⟨5619556862503, 5, [(2, 1), (3, 1), (11, 1), (19, 1), (4481305313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_4481305313
  · decide +kernel

theorem prime_5619556862629 : Nat.Prime 5619556862629 := by
  apply nodeValid_prime [2, 3, 30059, 15579241] ⟨5619556862629, 10, [(2, 2), (3, 1), (30059, 1), (15579241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30059
    · exact prime_15579241
  · decide +kernel

theorem prime_5619556991309 : Nat.Prime 5619556991309 := by
  apply nodeValid_prime [2, 13, 37, 2920767667] ⟨5619556991309, 2, [(2, 2), (13, 1), (37, 1), (2920767667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_2920767667
  · decide +kernel

theorem prime_5623753863463 : Nat.Prime 5623753863463 := by
  apply nodeValid_prime [2, 3, 7, 3329, 40221959] ⟨5623753863463, 3, [(2, 1), (3, 1), (7, 1), (3329, 1), (40221959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3329
    · exact prime_40221959
  · decide +kernel

theorem prime_5623753864693 : Nat.Prime 5623753864693 := by
  apply nodeValid_prime [2, 3, 468646155391] ⟨5623753864693, 2, [(2, 2), (3, 1), (468646155391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_468646155391
  · decide +kernel

theorem prime_5623753889261 : Nat.Prime 5623753889261 := by
  apply nodeValid_prime [2, 5, 13, 21629822651] ⟨5623753889261, 2, [(2, 2), (5, 1), (13, 1), (21629822651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_21629822651
  · decide +kernel

theorem prime_5627952843529 : Nat.Prime 5627952843529 := by
  apply nodeValid_prime [2, 3, 29, 131, 2693, 22921] ⟨5627952843529, 34, [(2, 3), (3, 1), (29, 1), (131, 1), (2693, 1), (22921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_131
    · exact prime_2693
    · exact prime_22921
  · decide +kernel

theorem prime_5627952845707 : Nat.Prime 5627952845707 := by
  apply nodeValid_prime [2, 3, 937992140951] ⟨5627952845707, 2, [(2, 1), (3, 1), (937992140951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_937992140951
  · decide +kernel

theorem prime_5627952922289 : Nat.Prime 5627952922289 := by
  apply nodeValid_prime [2, 619, 568250497] ⟨5627952922289, 3, [(2, 4), (619, 1), (568250497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_568250497
  · decide +kernel

theorem prime_5632153876969 : Nat.Prime 5632153876969 := by
  apply nodeValid_prime [2, 3, 31, 7570099297] ⟨5632153876969, 19, [(2, 3), (3, 1), (31, 1), (7570099297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_7570099297
  · decide +kernel

theorem prime_5632153877533 : Nat.Prime 5632153877533 := by
  apply nodeValid_prime [2, 3, 7, 13, 736807153] ⟨5632153877533, 2, [(2, 2), (3, 1), (7, 2), (13, 1), (736807153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_736807153
  · decide +kernel

theorem prime_5632154080321 : Nat.Prime 5632154080321 := by
  apply nodeValid_prime [2, 3, 5, 547, 10725461] ⟨5632154080321, 7, [(2, 6), (3, 1), (5, 1), (547, 1), (10725461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_547
    · exact prime_10725461
  · decide +kernel

theorem prime_5636357368567 : Nat.Prime 5636357368567 := by
  apply nodeValid_prime [2, 3, 653, 11821, 121697] ⟨5636357368567, 3, [(2, 1), (3, 1), (653, 1), (11821, 1), (121697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
    · exact prime_11821
    · exact prime_121697
  · decide +kernel

theorem prime_5636357504621 : Nat.Prime 5636357504621 := by
  apply nodeValid_prime [2, 5, 19, 23, 31, 359, 57947] ⟨5636357504621, 2, [(2, 2), (5, 1), (19, 1), (23, 1), (31, 1), (359, 1), (57947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_31
    · exact prime_359
    · exact prime_57947
  · decide +kernel

theorem prime_5636357505773 : Nat.Prime 5636357505773 := by
  apply nodeValid_prime [2, 7, 17, 4217, 165173] ⟨5636357505773, 2, [(2, 2), (7, 1), (17, 2), (4217, 1), (165173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_4217
    · exact prime_165173
  · decide +kernel

theorem prime_5640562779737 : Nat.Prime 5640562779737 := by
  apply nodeValid_prime [2, 31, 136991, 166027] ⟨5640562779737, 3, [(2, 3), (31, 1), (136991, 1), (166027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_136991
    · exact prime_166027
  · decide +kernel

theorem prime_5640562788187 : Nat.Prime 5640562788187 := by
  apply nodeValid_prime [2, 3, 19, 2333, 2711, 7823] ⟨5640562788187, 2, [(2, 1), (3, 1), (19, 1), (2333, 1), (2711, 1), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2333
    · exact prime_2711
    · exact prime_7823
  · decide +kernel

theorem prime_5640562788769 : Nat.Prime 5640562788769 := by
  apply nodeValid_prime [2, 3, 17, 1152075733] ⟨5640562788769, 7, [(2, 5), (3, 2), (17, 1), (1152075733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1152075733
  · decide +kernel

theorem prime_5644770141389 : Nat.Prime 5644770141389 := by
  apply nodeValid_prime [2, 7, 23, 499, 17565473] ⟨5644770141389, 2, [(2, 2), (7, 1), (23, 1), (499, 1), (17565473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_499
    · exact prime_17565473
  · decide +kernel

theorem prime_5644770142157 : Nat.Prime 5644770142157 := by
  apply nodeValid_prime [2, 1411192535539] ⟨5644770142157, 2, [(2, 2), (1411192535539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1411192535539
  · decide +kernel

theorem prime_5644770297139 : Nat.Prime 5644770297139 := by
  apply nodeValid_prime [2, 3, 7, 53, 845278571] ⟨5644770297139, 2, [(2, 1), (3, 2), (7, 1), (53, 1), (845278571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_845278571
  · decide +kernel

theorem prime_5648979934153 : Nat.Prime 5648979934153 := by
  apply nodeValid_prime [2, 3, 23, 251, 13590517] ⟨5648979934153, 5, [(2, 3), (3, 2), (23, 1), (251, 1), (13590517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_251
    · exact prime_13590517
  · decide +kernel

theorem prime_5648979974749 : Nat.Prime 5648979974749 := by
  apply nodeValid_prime [2, 3, 11, 42795302839] ⟨5648979974749, 2, [(2, 2), (3, 1), (11, 1), (42795302839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_42795302839
  · decide +kernel

theorem prime_5648979978253 : Nat.Prime 5648979978253 := by
  apply nodeValid_prime [2, 3, 13, 3463, 1161851] ⟨5648979978253, 2, [(2, 2), (3, 3), (13, 1), (3463, 1), (1161851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3463
    · exact prime_1161851
  · decide +kernel

theorem prime_5653191662927 : Nat.Prime 5653191662927 := by
  apply nodeValid_prime [2, 41, 110221, 625483] ⟨5653191662927, 5, [(2, 1), (41, 1), (110221, 1), (625483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_110221
    · exact prime_625483
  · decide +kernel

theorem prime_5653191663653 : Nat.Prime 5653191663653 := by
  apply nodeValid_prime [2, 13, 108715224301] ⟨5653191663653, 2, [(2, 2), (13, 1), (108715224301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_108715224301
  · decide +kernel

theorem prime_5653191682253 : Nat.Prime 5653191682253 := by
  apply nodeValid_prime [2, 293, 39511, 122081] ⟨5653191682253, 2, [(2, 2), (293, 1), (39511, 1), (122081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_39511
    · exact prime_122081
  · decide +kernel

theorem prime_5657405554043 : Nat.Prime 5657405554043 := by
  apply nodeValid_prime [2, 11, 163, 263, 545329] ⟨5657405554043, 2, [(2, 1), (11, 2), (163, 1), (263, 1), (545329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_163
    · exact prime_263
    · exact prime_545329
  · decide +kernel

theorem prime_5657405575769 : Nat.Prime 5657405575769 := by
  apply nodeValid_prime [2, 41, 281, 61381451] ⟨5657405575769, 6, [(2, 3), (41, 1), (281, 1), (61381451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_281
    · exact prime_61381451
  · decide +kernel

theorem prime_5657405576663 : Nat.Prime 5657405576663 := by
  apply nodeValid_prime [2, 7, 473923, 852671] ⟨5657405576663, 5, [(2, 1), (7, 1), (473923, 1), (852671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_473923
    · exact prime_852671
  · decide +kernel

theorem prime_5661621542329 : Nat.Prime 5661621542329 := by
  apply nodeValid_prime [2, 3, 235900897597] ⟨5661621542329, 31, [(2, 3), (3, 1), (235900897597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_235900897597
  · decide +kernel

theorem prime_5661621542453 : Nat.Prime 5661621542453 := by
  apply nodeValid_prime [2, 1171, 15647, 77249] ⟨5661621542453, 2, [(2, 2), (1171, 1), (15647, 1), (77249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1171
    · exact prime_15647
    · exact prime_77249
  · decide +kernel

theorem prime_5661621555437 : Nat.Prime 5661621555437 := by
  apply nodeValid_prime [2, 7, 11, 23, 131, 6100859] ⟨5661621555437, 2, [(2, 2), (7, 1), (11, 1), (23, 1), (131, 1), (6100859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_131
    · exact prime_6100859
  · decide +kernel

theorem prime_5665839689303 : Nat.Prime 5665839689303 := by
  apply nodeValid_prime [2, 13, 17, 79, 162261289] ⟨5665839689303, 5, [(2, 1), (13, 1), (17, 1), (79, 1), (162261289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_79
    · exact prime_162261289
  · decide +kernel

theorem prime_5665839713089 : Nat.Prime 5665839713089 := by
  apply nodeValid_prime [2, 3, 53, 21283, 26161] ⟨5665839713089, 7, [(2, 6), (3, 1), (53, 1), (21283, 1), (26161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_21283
    · exact prime_26161
  · decide +kernel

theorem prime_5665839714361 : Nat.Prime 5665839714361 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 53, 461, 5413] ⟨5665839714361, 13, [(2, 3), (3, 2), (5, 1), (7, 1), (17, 1), (53, 1), (461, 1), (5413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_53
    · exact prime_461
    · exact prime_5413
  · decide +kernel

end Sude.Lucas.Generated
