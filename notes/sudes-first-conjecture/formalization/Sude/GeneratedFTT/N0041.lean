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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0040

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7019 : Nat.Prime 7019 := by
  apply nodeValid_prime [2, 11, 29] ⟨7019, 2, [(2, 1), (11, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_9629 : Nat.Prime 9629 := by
  apply nodeValid_prime [2, 29, 83] ⟨9629, 2, [(2, 2), (29, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_83
  · decide +kernel

theorem prime_10957 : Nat.Prime 10957 := by
  apply nodeValid_prime [2, 3, 11, 83] ⟨10957, 5, [(2, 2), (3, 1), (11, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
  · decide +kernel

theorem prime_12163 : Nat.Prime 12163 := by
  apply nodeValid_prime [2, 3, 2027] ⟨12163, 5, [(2, 1), (3, 1), (2027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2027
  · decide +kernel

theorem prime_14387 : Nat.Prime 14387 := by
  apply nodeValid_prime [2, 7193] ⟨14387, 2, [(2, 1), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7193
  · decide +kernel

theorem prime_16823 : Nat.Prime 16823 := by
  apply nodeValid_prime [2, 13, 647] ⟨16823, 5, [(2, 1), (13, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_647
  · decide +kernel

theorem prime_18523 : Nat.Prime 18523 := by
  apply nodeValid_prime [2, 3, 7] ⟨18523, 3, [(2, 1), (3, 3), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_18593 : Nat.Prime 18593 := by
  apply nodeValid_prime [2, 7, 83] ⟨18593, 3, [(2, 5), (7, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_21139 : Nat.Prime 21139 := by
  apply nodeValid_prime [2, 3, 13, 271] ⟨21139, 2, [(2, 1), (3, 1), (13, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_271
  · decide +kernel

theorem prime_24593 : Nat.Prime 24593 := by
  apply nodeValid_prime [2, 29, 53] ⟨24593, 3, [(2, 4), (29, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_53
  · decide +kernel

theorem prime_26729 : Nat.Prime 26729 := by
  apply nodeValid_prime [2, 13, 257] ⟨26729, 3, [(2, 3), (13, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_257
  · decide +kernel

theorem prime_27017 : Nat.Prime 27017 := by
  apply nodeValid_prime [2, 11, 307] ⟨27017, 5, [(2, 3), (11, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_307
  · decide +kernel

theorem prime_31393 : Nat.Prime 31393 := by
  apply nodeValid_prime [2, 3, 109] ⟨31393, 5, [(2, 5), (3, 2), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
  · decide +kernel

theorem prime_33119 : Nat.Prime 33119 := by
  apply nodeValid_prime [2, 29, 571] ⟨33119, 7, [(2, 1), (29, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_571
  · decide +kernel

theorem prime_33647 : Nat.Prime 33647 := by
  apply nodeValid_prime [2, 16823] ⟨33647, 5, [(2, 1), (16823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16823
  · decide +kernel

theorem prime_34613 : Nat.Prime 34613 := by
  apply nodeValid_prime [2, 17, 509] ⟨34613, 2, [(2, 2), (17, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_509
  · decide +kernel

theorem prime_35999 : Nat.Prime 35999 := by
  apply nodeValid_prime [2, 41, 439] ⟨35999, 13, [(2, 1), (41, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_439
  · decide +kernel

theorem prime_40867 : Nat.Prime 40867 := by
  apply nodeValid_prime [2, 3, 7, 139] ⟨40867, 2, [(2, 1), (3, 1), (7, 2), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_42391 : Nat.Prime 42391 := by
  apply nodeValid_prime [2, 3, 5, 157] ⟨42391, 6, [(2, 1), (3, 3), (5, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
  · decide +kernel

theorem prime_43487 : Nat.Prime 43487 := by
  apply nodeValid_prime [2, 17, 1279] ⟨43487, 5, [(2, 1), (17, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1279
  · decide +kernel

theorem prime_45281 : Nat.Prime 45281 := by
  apply nodeValid_prime [2, 5, 283] ⟨45281, 3, [(2, 5), (5, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_283
  · decide +kernel

theorem prime_50587 : Nat.Prime 50587 := by
  apply nodeValid_prime [2, 3, 8431] ⟨50587, 14, [(2, 1), (3, 1), (8431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8431
  · decide +kernel

theorem prime_55009 : Nat.Prime 55009 := by
  apply nodeValid_prime [2, 3, 191] ⟨55009, 7, [(2, 5), (3, 2), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
  · decide +kernel

theorem prime_69163 : Nat.Prime 69163 := by
  apply nodeValid_prime [2, 3, 11527] ⟨69163, 2, [(2, 1), (3, 1), (11527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11527
  · decide +kernel

theorem prime_71999 : Nat.Prime 71999 := by
  apply nodeValid_prime [2, 35999] ⟨71999, 7, [(2, 1), (35999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35999
  · decide +kernel

theorem prime_84457 : Nat.Prime 84457 := by
  apply nodeValid_prime [2, 3, 17, 23] ⟨84457, 5, [(2, 3), (3, 3), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_96233 : Nat.Prime 96233 := by
  apply nodeValid_prime [2, 23, 523] ⟨96233, 3, [(2, 3), (23, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_523
  · decide +kernel

theorem prime_114043 : Nat.Prime 114043 := by
  apply nodeValid_prime [2, 3, 83, 229] ⟨114043, 2, [(2, 1), (3, 1), (83, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_229
  · decide +kernel

theorem prime_114691 : Nat.Prime 114691 := by
  apply nodeValid_prime [2, 3, 5, 3823] ⟨114691, 2, [(2, 1), (3, 1), (5, 1), (3823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3823
  · decide +kernel

theorem prime_118171 : Nat.Prime 118171 := by
  apply nodeValid_prime [2, 3, 5, 13, 101] ⟨118171, 7, [(2, 1), (3, 2), (5, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_126757 : Nat.Prime 126757 := by
  apply nodeValid_prime [2, 3, 7, 503] ⟨126757, 2, [(2, 2), (3, 2), (7, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_503
  · decide +kernel

theorem prime_129953 : Nat.Prime 129953 := by
  apply nodeValid_prime [2, 31, 131] ⟨129953, 3, [(2, 5), (31, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_131
  · decide +kernel

theorem prime_150211 : Nat.Prime 150211 := by
  apply nodeValid_prime [2, 3, 5, 1669] ⟨150211, 2, [(2, 1), (3, 2), (5, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1669
  · decide +kernel

theorem prime_157327 : Nat.Prime 157327 := by
  apply nodeValid_prime [2, 3, 13, 2017] ⟨157327, 3, [(2, 1), (3, 1), (13, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2017
  · decide +kernel

theorem prime_161531 : Nat.Prime 161531 := by
  apply nodeValid_prime [2, 5, 29, 557] ⟨161531, 2, [(2, 1), (5, 1), (29, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_557
  · decide +kernel

theorem prime_176983 : Nat.Prime 176983 := by
  apply nodeValid_prime [2, 3, 13, 2269] ⟨176983, 3, [(2, 1), (3, 1), (13, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2269
  · decide +kernel

theorem prime_190889 : Nat.Prime 190889 := by
  apply nodeValid_prime [2, 107, 223] ⟨190889, 3, [(2, 3), (107, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_223
  · decide +kernel

theorem prime_196187 : Nat.Prime 196187 := by
  apply nodeValid_prime [2, 233, 421] ⟨196187, 2, [(2, 1), (233, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_233
    · exact prime_421
  · decide +kernel

theorem prime_268003 : Nat.Prime 268003 := by
  apply nodeValid_prime [2, 3, 7, 709] ⟨268003, 2, [(2, 1), (3, 3), (7, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_709
  · decide +kernel

theorem prime_282127 : Nat.Prime 282127 := by
  apply nodeValid_prime [2, 3, 13, 3617] ⟨282127, 3, [(2, 1), (3, 1), (13, 1), (3617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3617
  · decide +kernel

theorem prime_293147 : Nat.Prime 293147 := by
  apply nodeValid_prime [2, 7, 20939] ⟨293147, 2, [(2, 1), (7, 1), (20939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_20939
  · decide +kernel

theorem prime_305243 : Nat.Prime 305243 := by
  apply nodeValid_prime [2, 7, 21803] ⟨305243, 2, [(2, 1), (7, 1), (21803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_21803
  · decide +kernel

theorem prime_308309 : Nat.Prime 308309 := by
  apply nodeValid_prime [2, 7, 11, 13] ⟨308309, 2, [(2, 2), (7, 2), (11, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_333721 : Nat.Prime 333721 := by
  apply nodeValid_prime [2, 3, 5, 103] ⟨333721, 13, [(2, 3), (3, 4), (5, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_453553 : Nat.Prime 453553 := by
  apply nodeValid_prime [2, 3, 11, 859] ⟨453553, 10, [(2, 4), (3, 1), (11, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_859
  · decide +kernel

theorem prime_463973 : Nat.Prime 463973 := by
  apply nodeValid_prime [2, 193, 601] ⟨463973, 2, [(2, 2), (193, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_601
  · decide +kernel

theorem prime_584663 : Nat.Prime 584663 := by
  apply nodeValid_prime [2, 13, 113, 199] ⟨584663, 5, [(2, 1), (13, 1), (113, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
    · exact prime_199
  · decide +kernel

theorem prime_688147 : Nat.Prime 688147 := by
  apply nodeValid_prime [2, 3, 114691] ⟨688147, 2, [(2, 1), (3, 1), (114691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_114691
  · decide +kernel

theorem prime_912799 : Nat.Prime 912799 := by
  apply nodeValid_prime [2, 3, 17, 19, 157] ⟨912799, 6, [(2, 1), (3, 2), (17, 1), (19, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_157
  · decide +kernel

theorem prime_1128509 : Nat.Prime 1128509 := by
  apply nodeValid_prime [2, 282127] ⟨1128509, 2, [(2, 2), (282127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_282127
  · decide +kernel

theorem prime_1152091 : Nat.Prime 1152091 := by
  apply nodeValid_prime [2, 3, 5, 17, 251] ⟨1152091, 3, [(2, 1), (3, 3), (5, 1), (17, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_251
  · decide +kernel

theorem prime_1446257 : Nat.Prime 1446257 := by
  apply nodeValid_prime [2, 7, 37, 349] ⟨1446257, 3, [(2, 4), (7, 1), (37, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_349
  · decide +kernel

theorem prime_1622207 : Nat.Prime 1622207 := by
  apply nodeValid_prime [2, 41, 73, 271] ⟨1622207, 5, [(2, 1), (41, 1), (73, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_73
    · exact prime_271
  · decide +kernel

theorem prime_1791077 : Nat.Prime 1791077 := by
  apply nodeValid_prime [2, 7, 47, 1361] ⟨1791077, 2, [(2, 2), (7, 1), (47, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_1361
  · decide +kernel

theorem prime_2128387 : Nat.Prime 2128387 := by
  apply nodeValid_prime [2, 3, 13, 2099] ⟨2128387, 2, [(2, 1), (3, 1), (13, 2), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2099
  · decide +kernel

theorem prime_2156897 : Nat.Prime 2156897 := by
  apply nodeValid_prime [2, 7, 9629] ⟨2156897, 3, [(2, 5), (7, 1), (9629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9629
  · decide +kernel

theorem prime_2458679 : Nat.Prime 2458679 := by
  apply nodeValid_prime [2, 29, 42391] ⟨2458679, 11, [(2, 1), (29, 1), (42391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_42391
  · decide +kernel

theorem prime_2619761 : Nat.Prime 2619761 := by
  apply nodeValid_prime [2, 5, 11, 13, 229] ⟨2619761, 6, [(2, 4), (5, 1), (11, 1), (13, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_229
  · decide +kernel

theorem prime_2624467 : Nat.Prime 2624467 := by
  apply nodeValid_prime [2, 3, 13, 33647] ⟨2624467, 2, [(2, 1), (3, 1), (13, 1), (33647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_33647
  · decide +kernel

theorem prime_2698109 : Nat.Prime 2698109 := by
  apply nodeValid_prime [2, 7, 173, 557] ⟨2698109, 3, [(2, 2), (7, 1), (173, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_173
    · exact prime_557
  · decide +kernel

theorem prime_2710681 : Nat.Prime 2710681 := by
  apply nodeValid_prime [2, 3, 5, 7, 461] ⟨2710681, 19, [(2, 3), (3, 1), (5, 1), (7, 2), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_461
  · decide +kernel

theorem prime_2910199 : Nat.Prime 2910199 := by
  apply nodeValid_prime [2, 3, 37, 13109] ⟨2910199, 3, [(2, 1), (3, 1), (37, 1), (13109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_13109
  · decide +kernel

theorem prime_3337211 : Nat.Prime 3337211 := by
  apply nodeValid_prime [2, 5, 333721] ⟨3337211, 2, [(2, 1), (5, 1), (333721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_333721
  · decide +kernel

theorem prime_4890871 : Nat.Prime 4890871 := by
  apply nodeValid_prime [2, 3, 5, 31, 1753] ⟨4890871, 6, [(2, 1), (3, 2), (5, 1), (31, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_1753
  · decide +kernel

theorem prime_4970569 : Nat.Prime 4970569 := by
  apply nodeValid_prime [2, 3, 71, 2917] ⟨4970569, 11, [(2, 3), (3, 1), (71, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_2917
  · decide +kernel

theorem prime_7107179 : Nat.Prime 7107179 := by
  apply nodeValid_prime [2, 13, 19, 14387] ⟨7107179, 2, [(2, 1), (13, 1), (19, 1), (14387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_14387
  · decide +kernel

theorem prime_7186523 : Nat.Prime 7186523 := by
  apply nodeValid_prime [2, 7, 19, 27017] ⟨7186523, 2, [(2, 1), (7, 1), (19, 1), (27017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_27017
  · decide +kernel

theorem prime_9775307 : Nat.Prime 9775307 := by
  apply nodeValid_prime [2, 17, 107, 2687] ⟨9775307, 5, [(2, 1), (17, 1), (107, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_107
    · exact prime_2687
  · decide +kernel

theorem prime_14214359 : Nat.Prime 14214359 := by
  apply nodeValid_prime [2, 7107179] ⟨14214359, 11, [(2, 1), (7107179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7107179
  · decide +kernel

theorem prime_15845593 : Nat.Prime 15845593 := by
  apply nodeValid_prime [2, 3, 7, 257, 367] ⟨15845593, 5, [(2, 3), (3, 1), (7, 1), (257, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_257
    · exact prime_367
  · decide +kernel

theorem prime_16461931 : Nat.Prime 16461931 := by
  apply nodeValid_prime [2, 3, 5, 31, 571] ⟨16461931, 3, [(2, 1), (3, 1), (5, 1), (31, 2), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_571
  · decide +kernel

theorem prime_21979807 : Nat.Prime 21979807 := by
  apply nodeValid_prime [2, 3, 31, 118171] ⟨21979807, 3, [(2, 1), (3, 1), (31, 1), (118171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_118171
  · decide +kernel

theorem prime_23858423 : Nat.Prime 23858423 := by
  apply nodeValid_prime [2, 7, 47, 101, 359] ⟨23858423, 5, [(2, 1), (7, 1), (47, 1), (101, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_101
    · exact prime_359
  · decide +kernel

theorem prime_32190091 : Nat.Prime 32190091 := by
  apply nodeValid_prime [2, 3, 5, 31, 34613] ⟨32190091, 12, [(2, 1), (3, 1), (5, 1), (31, 1), (34613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_34613
  · decide +kernel

theorem prime_35143091 : Nat.Prime 35143091 := by
  apply nodeValid_prime [2, 5, 881, 3989] ⟨35143091, 2, [(2, 1), (5, 1), (881, 1), (3989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_881
    · exact prime_3989
  · decide +kernel

theorem prime_40774511 : Nat.Prime 40774511 := by
  apply nodeValid_prime [2, 5, 7, 313, 1861] ⟨40774511, 7, [(2, 1), (5, 1), (7, 1), (313, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_313
    · exact prime_1861
  · decide +kernel

theorem prime_47240407 : Nat.Prime 47240407 := by
  apply nodeValid_prime [2, 3, 2624467] ⟨47240407, 5, [(2, 1), (3, 2), (2624467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2624467
  · decide +kernel

theorem prime_55055267 : Nat.Prime 55055267 := by
  apply nodeValid_prime [2, 7, 1409, 2791] ⟨55055267, 2, [(2, 1), (7, 1), (1409, 1), (2791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1409
    · exact prime_2791
  · decide +kernel

theorem prime_98771587 : Nat.Prime 98771587 := by
  apply nodeValid_prime [2, 3, 16461931] ⟨98771587, 3, [(2, 1), (3, 1), (16461931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16461931
  · decide +kernel

theorem prime_112073011 : Nat.Prime 112073011 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 31393] ⟨112073011, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (31393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_31393
  · decide +kernel

theorem prime_140636959 : Nat.Prime 140636959 := by
  apply nodeValid_prime [2, 3, 7, 11, 43487] ⟨140636959, 6, [(2, 1), (3, 1), (7, 2), (11, 1), (43487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_43487
  · decide +kernel

theorem prime_161422007 : Nat.Prime 161422007 := by
  apply nodeValid_prime [2, 2437, 33119] ⟨161422007, 5, [(2, 1), (2437, 1), (33119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2437
    · exact prime_33119
  · decide +kernel

theorem prime_173969603 : Nat.Prime 173969603 := by
  apply nodeValid_prime [2, 17, 113, 45281] ⟨173969603, 2, [(2, 1), (17, 1), (113, 1), (45281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_113
    · exact prime_45281
  · decide +kernel

theorem prime_199001027 : Nat.Prime 199001027 := by
  apply nodeValid_prime [2, 7, 14214359] ⟨199001027, 2, [(2, 1), (7, 1), (14214359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_14214359
  · decide +kernel

theorem prime_202070867 : Nat.Prime 202070867 := by
  apply nodeValid_prime [2, 331, 305243] ⟨202070867, 2, [(2, 1), (331, 1), (305243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_331
    · exact prime_305243
  · decide +kernel

theorem prime_293452261 : Nat.Prime 293452261 := by
  apply nodeValid_prime [2, 3, 5, 4890871] ⟨293452261, 10, [(2, 2), (3, 1), (5, 1), (4890871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4890871
  · decide +kernel

theorem prime_338187677 : Nat.Prime 338187677 := by
  apply nodeValid_prime [2, 23, 29, 126757] ⟨338187677, 2, [(2, 2), (23, 1), (29, 1), (126757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29
    · exact prime_126757
  · decide +kernel

theorem prime_531802703 : Nat.Prime 531802703 := by
  apply nodeValid_prime [2, 37, 7186523] ⟨531802703, 5, [(2, 1), (37, 1), (7186523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_7186523
  · decide +kernel

theorem prime_706537831 : Nat.Prime 706537831 := by
  apply nodeValid_prime [2, 3, 5, 41, 127, 4523] ⟨706537831, 3, [(2, 1), (3, 1), (5, 1), (41, 1), (127, 1), (4523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_127
    · exact prime_4523
  · decide +kernel

theorem prime_715350791 : Nat.Prime 715350791 := by
  apply nodeValid_prime [2, 5, 7, 11, 84457] ⟨715350791, 7, [(2, 1), (5, 1), (7, 1), (11, 2), (84457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_84457
  · decide +kernel

theorem prime_1020483979 : Nat.Prime 1020483979 := by
  apply nodeValid_prime [2, 3, 31, 176983] ⟨1020483979, 3, [(2, 1), (3, 1), (31, 2), (176983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_176983
  · decide +kernel

theorem prime_1208686481 : Nat.Prime 1208686481 := by
  apply nodeValid_prime [2, 5, 157, 96233] ⟨1208686481, 3, [(2, 4), (5, 1), (157, 1), (96233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_96233
  · decide +kernel

theorem prime_1702307669 : Nat.Prime 1702307669 := by
  apply nodeValid_prime [2, 157, 2710681] ⟨1702307669, 2, [(2, 2), (157, 1), (2710681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_2710681
  · decide +kernel

theorem prime_1736144647 : Nat.Prime 1736144647 := by
  apply nodeValid_prime [2, 3, 19, 31, 223, 2203] ⟨1736144647, 5, [(2, 1), (3, 1), (19, 1), (31, 1), (223, 1), (2203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_223
    · exact prime_2203
  · decide +kernel

theorem prime_2029126063 : Nat.Prime 2029126063 := by
  apply nodeValid_prime [2, 3, 338187677] ⟨2029126063, 5, [(2, 1), (3, 1), (338187677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_338187677
  · decide +kernel

theorem prime_2848928581 : Nat.Prime 2848928581 := by
  apply nodeValid_prime [2, 3, 5, 23, 688147] ⟨2848928581, 14, [(2, 2), (3, 2), (5, 1), (23, 1), (688147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_688147
  · decide +kernel

theorem prime_12174756379 : Nat.Prime 12174756379 := by
  apply nodeValid_prime [2, 3, 2029126063] ⟨12174756379, 7, [(2, 1), (3, 1), (2029126063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2029126063
  · decide +kernel

theorem prime_16032613327 : Nat.Prime 16032613327 := by
  apply nodeValid_prime [2, 3, 19, 140636959] ⟨16032613327, 3, [(2, 1), (3, 1), (19, 1), (140636959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_140636959
  · decide +kernel

theorem prime_16107564841 : Nat.Prime 16107564841 := by
  apply nodeValid_prime [2, 3, 5, 61, 101, 21787] ⟨16107564841, 17, [(2, 3), (3, 1), (5, 1), (61, 1), (101, 1), (21787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_101
    · exact prime_21787
  · decide +kernel

theorem prime_42261678593 : Nat.Prime 42261678593 := by
  apply nodeValid_prime [2, 7, 73, 161531] ⟨42261678593, 3, [(2, 9), (7, 1), (73, 1), (161531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_161531
  · decide +kernel

theorem prime_42326941427 : Nat.Prime 42326941427 := by
  apply nodeValid_prime [2, 7, 11, 1747, 157327] ⟨42326941427, 5, [(2, 1), (7, 1), (11, 1), (1747, 1), (157327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1747
    · exact prime_157327
  · decide +kernel

theorem prime_289485977411 : Nat.Prime 289485977411 := by
  apply nodeValid_prime [2, 5, 7, 59, 67, 103, 1451] ⟨289485977411, 2, [(2, 1), (5, 1), (7, 2), (59, 1), (67, 1), (103, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_67
    · exact prime_103
    · exact prime_1451
  · decide +kernel

theorem prime_292647210899 : Nat.Prime 292647210899 := by
  apply nodeValid_prime [2, 7, 18523, 1128509] ⟨292647210899, 2, [(2, 1), (7, 1), (18523, 1), (1128509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_18523
    · exact prime_1128509
  · decide +kernel

theorem prime_295375374113 : Nat.Prime 295375374113 := by
  apply nodeValid_prime [2, 7, 13, 29, 4159] ⟨295375374113, 3, [(2, 5), (7, 1), (13, 1), (29, 3), (4159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_4159
  · decide +kernel

theorem prime_573589670273 : Nat.Prime 573589670273 := by
  apply nodeValid_prime [2, 34483, 129953] ⟨573589670273, 3, [(2, 7), (34483, 1), (129953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_34483
    · exact prime_129953
  · decide +kernel

theorem prime_573589670299 : Nat.Prime 573589670299 := by
  apply nodeValid_prime [2, 3, 853, 112073011] ⟨573589670299, 3, [(2, 1), (3, 1), (853, 1), (112073011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_853
    · exact prime_112073011
  · decide +kernel

theorem prime_573589684303 : Nat.Prime 573589684303 := by
  apply nodeValid_prime [2, 3, 31, 1901, 1622207] ⟨573589684303, 3, [(2, 1), (3, 1), (31, 1), (1901, 1), (1622207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_1901
    · exact prime_1622207
  · decide +kernel

theorem prime_574484365597 : Nat.Prime 574484365597 := by
  apply nodeValid_prime [2, 3, 26729, 1791077] ⟨574484365597, 2, [(2, 2), (3, 1), (26729, 1), (1791077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26729
    · exact prime_1791077
  · decide +kernel

theorem prime_574484401159 : Nat.Prime 574484401159 := by
  apply nodeValid_prime [2, 3, 151, 11527, 55009] ⟨574484401159, 3, [(2, 1), (3, 1), (151, 1), (11527, 1), (55009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_11527
    · exact prime_55009
  · decide +kernel

theorem prime_574484401837 : Nat.Prime 574484401837 := by
  apply nodeValid_prime [2, 3, 17, 7019, 44579] ⟨574484401837, 5, [(2, 2), (3, 3), (17, 1), (7019, 1), (44579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_7019
    · exact prime_44579
  · decide +kernel

theorem prime_575379992123 : Nat.Prime 575379992123 := by
  apply nodeValid_prime [2, 13, 1702307669] ⟨575379992123, 2, [(2, 1), (13, 2), (1702307669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1702307669
  · decide +kernel

theorem prime_575380007471 : Nat.Prime 575380007471 := by
  apply nodeValid_prime [2, 5, 239, 2111, 114043] ⟨575380007471, 11, [(2, 1), (5, 1), (239, 1), (2111, 1), (114043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_2111
    · exact prime_114043
  · decide +kernel

theorem prime_575380007533 : Nat.Prime 575380007533 := by
  apply nodeValid_prime [2, 3, 11, 17, 7027, 12163] ⟨575380007533, 6, [(2, 2), (3, 2), (11, 1), (17, 1), (7027, 1), (12163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_7027
    · exact prime_12163
  · decide +kernel

theorem prime_576276564991 : Nat.Prime 576276564991 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 161422007] ⟨576276564991, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (161422007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_161422007
  · decide +kernel

theorem prime_576276593929 : Nat.Prime 576276593929 := by
  apply nodeValid_prime [2, 3, 7, 5867, 584663] ⟨576276593929, 17, [(2, 3), (3, 1), (7, 1), (5867, 1), (584663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5867
    · exact prime_584663
  · decide +kernel

theorem prime_576276594359 : Nat.Prime 576276594359 := by
  apply nodeValid_prime [2, 29, 271, 1301, 28181] ⟨576276594359, 7, [(2, 1), (29, 1), (271, 1), (1301, 1), (28181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_271
    · exact prime_1301
    · exact prime_28181
  · decide +kernel

theorem prime_577174079773 : Nat.Prime 577174079773 := by
  apply nodeValid_prime [2, 3, 16032613327] ⟨577174079773, 2, [(2, 2), (3, 2), (16032613327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16032613327
  · decide +kernel

theorem prime_577174080169 : Nat.Prime 577174080169 := by
  apply nodeValid_prime [2, 3, 7, 37, 139, 2749] ⟨577174080169, 13, [(2, 3), (3, 6), (7, 1), (37, 1), (139, 1), (2749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_139
    · exact prime_2749
  · decide +kernel

theorem prime_577174081063 : Nat.Prime 577174081063 := by
  apply nodeValid_prime [2, 3, 101, 353, 2698109] ⟨577174081063, 3, [(2, 1), (3, 1), (101, 1), (353, 1), (2698109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_353
    · exact prime_2698109
  · decide +kernel

theorem prime_578072542273 : Nat.Prime 578072542273 := by
  apply nodeValid_prime [2, 3, 40867, 73673] ⟨578072542273, 10, [(2, 6), (3, 1), (40867, 1), (73673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40867
    · exact prime_73673
  · decide +kernel

theorem prime_578072592001 : Nat.Prime 578072592001 := by
  apply nodeValid_prime [2, 3, 5, 293, 4567] ⟨578072592001, 13, [(2, 7), (3, 3), (5, 3), (293, 1), (4567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_4567
  · decide +kernel

theorem prime_578072592203 : Nat.Prime 578072592203 := by
  apply nodeValid_prime [2, 7, 199, 673, 308309] ⟨578072592203, 2, [(2, 1), (7, 1), (199, 1), (673, 1), (308309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_199
    · exact prime_673
    · exact prime_308309
  · decide +kernel

theorem prime_578971882997 : Nat.Prime 578971882997 := by
  apply nodeValid_prime [2, 13, 17, 67, 9775307] ⟨578971882997, 2, [(2, 2), (13, 1), (17, 1), (67, 1), (9775307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_67
    · exact prime_9775307
  · decide +kernel

theorem prime_578971954823 : Nat.Prime 578971954823 := by
  apply nodeValid_prime [2, 289485977411] ⟨578971954823, 5, [(2, 1), (289485977411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_289485977411
  · decide +kernel

theorem prime_579872312099 : Nat.Prime 579872312099 := by
  apply nodeValid_prime [2, 167, 1736144647] ⟨579872312099, 2, [(2, 1), (167, 1), (1736144647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_1736144647
  · decide +kernel

theorem prime_579872334277 : Nat.Prime 579872334277 := by
  apply nodeValid_prime [2, 3, 16107564841] ⟨579872334277, 2, [(2, 2), (3, 2), (16107564841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16107564841
  · decide +kernel

theorem prime_579872335051 : Nat.Prime 579872335051 := by
  apply nodeValid_prime [2, 3, 5, 20389, 21067] ⟨579872335051, 3, [(2, 1), (3, 3), (5, 2), (20389, 1), (21067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20389
    · exact prime_21067
  · decide +kernel

theorem prime_580773563021 : Nat.Prime 580773563021 := by
  apply nodeValid_prime [2, 5, 7, 8941, 463973] ⟨580773563021, 3, [(2, 2), (5, 1), (7, 1), (8941, 1), (463973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_8941
    · exact prime_463973
  · decide +kernel

theorem prime_580773563659 : Nat.Prime 580773563659 := by
  apply nodeValid_prime [2, 3, 683, 47240407] ⟨580773563659, 3, [(2, 1), (3, 2), (683, 1), (47240407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_683
    · exact prime_47240407
  · decide +kernel

theorem prime_580773621823 : Nat.Prime 580773621823 := by
  apply nodeValid_prime [2, 3, 31, 97, 32190091] ⟨580773621823, 5, [(2, 1), (3, 1), (31, 1), (97, 1), (32190091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_97
    · exact prime_32190091
  · decide +kernel

theorem prime_581675866657 : Nat.Prime 581675866657 := by
  apply nodeValid_prime [2, 3, 23, 53, 4970569] ⟨581675866657, 5, [(2, 5), (3, 1), (23, 1), (53, 1), (4970569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53
    · exact prime_4970569
  · decide +kernel

theorem prime_581675868031 : Nat.Prime 581675868031 := by
  apply nodeValid_prime [2, 3, 5, 19, 1020483979] ⟨581675868031, 6, [(2, 1), (3, 1), (5, 1), (19, 1), (1020483979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1020483979
  · decide +kernel

theorem prime_581675877301 : Nat.Prime 581675877301 := by
  apply nodeValid_prime [2, 3, 5, 7, 83, 3337211] ⟨581675877301, 10, [(2, 2), (3, 1), (5, 2), (7, 1), (83, 1), (3337211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_83
    · exact prime_3337211
  · decide +kernel

theorem prime_582579071693 : Nat.Prime 582579071693 := by
  apply nodeValid_prime [2, 37, 1601, 2458679] ⟨582579071693, 2, [(2, 2), (37, 1), (1601, 1), (2458679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1601
    · exact prime_2458679
  · decide +kernel

theorem prime_582579072239 : Nat.Prime 582579072239 := by
  apply nodeValid_prime [2, 31, 593, 15845593] ⟨582579072239, 13, [(2, 1), (31, 1), (593, 1), (15845593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_593
    · exact prime_15845593
  · decide +kernel

theorem prime_582579082669 : Nat.Prime 582579082669 := by
  apply nodeValid_prime [2, 3, 11, 17, 107, 787, 3083] ⟨582579082669, 2, [(2, 2), (3, 1), (11, 1), (17, 1), (107, 1), (787, 1), (3083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_107
    · exact prime_787
    · exact prime_3083
  · decide +kernel

theorem prime_583483235017 : Nat.Prime 583483235017 := by
  apply nodeValid_prime [2, 3, 11, 443, 453553] ⟨583483235017, 17, [(2, 3), (3, 1), (11, 2), (443, 1), (453553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_443
    · exact prime_453553
  · decide +kernel

theorem prime_583483252223 : Nat.Prime 583483252223 := by
  apply nodeValid_prime [2, 13, 89, 9433, 26731] ⟨583483252223, 5, [(2, 1), (13, 1), (89, 1), (9433, 1), (26731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_89
    · exact prime_9433
    · exact prime_26731
  · decide +kernel

theorem prime_583483252411 : Nat.Prime 583483252411 := by
  apply nodeValid_prime [2, 3, 5, 53, 40774511] ⟨583483252411, 3, [(2, 1), (3, 3), (5, 1), (53, 1), (40774511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_40774511
  · decide +kernel

theorem prime_584388306193 : Nat.Prime 584388306193 := by
  apply nodeValid_prime [2, 3, 12174756379] ⟨584388306193, 5, [(2, 4), (3, 1), (12174756379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12174756379
  · decide +kernel

theorem prime_584388307147 : Nat.Prime 584388307147 := by
  apply nodeValid_prime [2, 3, 7, 967, 2689, 5351] ⟨584388307147, 2, [(2, 1), (3, 1), (7, 1), (967, 1), (2689, 1), (5351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_967
    · exact prime_2689
    · exact prime_5351
  · decide +kernel

theorem prime_584388348157 : Nat.Prime 584388348157 := by
  apply nodeValid_prime [2, 3, 277, 307, 190889] ⟨584388348157, 2, [(2, 2), (3, 2), (277, 1), (307, 1), (190889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_307
    · exact prime_190889
  · decide +kernel

theorem prime_585294414799 : Nat.Prime 585294414799 := by
  apply nodeValid_prime [2, 3, 1021, 1327, 71999] ⟨585294414799, 3, [(2, 1), (3, 1), (1021, 1), (1327, 1), (71999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
    · exact prime_1327
    · exact prime_71999
  · decide +kernel

theorem prime_585294421799 : Nat.Prime 585294421799 := by
  apply nodeValid_prime [2, 292647210899] ⟨585294421799, 19, [(2, 1), (292647210899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_292647210899
  · decide +kernel

theorem prime_585294422873 : Nat.Prime 585294422873 := by
  apply nodeValid_prime [2, 50587, 1446257] ⟨585294422873, 3, [(2, 3), (50587, 1), (1446257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_50587
    · exact prime_1446257
  · decide +kernel

theorem prime_586201431721 : Nat.Prime 586201431721 := by
  apply nodeValid_prime [2, 3, 5, 17, 1913, 150211] ⟨586201431721, 14, [(2, 3), (3, 1), (5, 1), (17, 1), (1913, 1), (150211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_1913
    · exact prime_150211
  · decide +kernel

theorem prime_586201452691 : Nat.Prime 586201452691 := by
  apply nodeValid_prime [2, 3, 5, 7, 127, 21979807] ⟨586201452691, 15, [(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (21979807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_127
    · exact prime_21979807
  · decide +kernel

theorem prime_586201453111 : Nat.Prime 586201453111 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 23858423] ⟨586201453111, 3, [(2, 1), (3, 3), (5, 1), (7, 1), (13, 1), (23858423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_23858423
  · decide +kernel

theorem prime_587109366659 : Nat.Prime 587109366659 := by
  apply nodeValid_prime [2, 19, 5309, 2910199] ⟨587109366659, 2, [(2, 1), (19, 1), (5309, 1), (2910199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_5309
    · exact prime_2910199
  · decide +kernel

theorem prime_587109367289 : Nat.Prime 587109367289 := by
  apply nodeValid_prime [2, 31, 43, 55055267] ⟨587109367289, 3, [(2, 3), (31, 1), (43, 1), (55055267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_55055267
  · decide +kernel

theorem prime_587109398189 : Nat.Prime 587109398189 := by
  apply nodeValid_prime [2, 179, 313, 2619761] ⟨587109398189, 2, [(2, 2), (179, 1), (313, 1), (2619761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_313
    · exact prime_2619761
  · decide +kernel

theorem prime_588018313471 : Nat.Prime 588018313471 := by
  apply nodeValid_prime [2, 3, 5, 7, 73, 2063, 18593] ⟨588018313471, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (2063, 1), (18593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_73
    · exact prime_2063
    · exact prime_18593
  · decide +kernel

theorem prime_588018346759 : Nat.Prime 588018346759 := by
  apply nodeValid_prime [2, 3, 73, 2281, 196187] ⟨588018346759, 3, [(2, 1), (3, 2), (73, 1), (2281, 1), (196187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_2281
    · exact prime_196187
  · decide +kernel

theorem prime_588018350203 : Nat.Prime 588018350203 := by
  apply nodeValid_prime [2, 3, 137, 715350791] ⟨588018350203, 2, [(2, 1), (3, 1), (137, 1), (715350791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_715350791
  · decide +kernel

theorem prime_588928181563 : Nat.Prime 588928181563 := by
  apply nodeValid_prime [2, 3, 7, 4057, 1152091] ⟨588928181563, 2, [(2, 1), (3, 2), (7, 1), (4057, 1), (1152091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4057
    · exact prime_1152091
  · decide +kernel

theorem prime_588928218943 : Nat.Prime 588928218943 := by
  apply nodeValid_prime [2, 3, 7, 31, 1543, 293147] ⟨588928218943, 3, [(2, 1), (3, 1), (7, 1), (31, 1), (1543, 1), (293147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_1543
    · exact prime_293147
  · decide +kernel

theorem prime_588928219129 : Nat.Prime 588928219129 := by
  apply nodeValid_prime [2, 3, 31, 43, 499, 4099] ⟨588928219129, 7, [(2, 3), (3, 3), (31, 1), (43, 1), (499, 1), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
    · exact prime_499
    · exact prime_4099
  · decide +kernel

theorem prime_589839002729 : Nat.Prime 589839002729 := by
  apply nodeValid_prime [2, 61, 1208686481] ⟨589839002729, 3, [(2, 3), (61, 1), (1208686481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_1208686481
  · decide +kernel

theorem prime_589839044029 : Nat.Prime 589839044029 := by
  apply nodeValid_prime [2, 3, 13, 19, 199001027] ⟨589839044029, 2, [(2, 2), (3, 1), (13, 1), (19, 1), (199001027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_199001027
  · decide +kernel

theorem prime_589839044611 : Nat.Prime 589839044611 := by
  apply nodeValid_prime [2, 3, 5, 67, 293452261] ⟨589839044611, 3, [(2, 1), (3, 1), (5, 1), (67, 1), (293452261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_293452261
  · decide +kernel

theorem prime_590750747669 : Nat.Prime 590750747669 := by
  apply nodeValid_prime [2, 23, 47, 281, 21139] ⟨590750747669, 2, [(2, 2), (23, 2), (47, 1), (281, 1), (21139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_281
    · exact prime_21139
  · decide +kernel

theorem prime_590750748227 : Nat.Prime 590750748227 := by
  apply nodeValid_prime [2, 295375374113] ⟨590750748227, 2, [(2, 1), (295375374113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_295375374113
  · decide +kernel

theorem prime_590750774833 : Nat.Prime 590750774833 := by
  apply nodeValid_prime [2, 3, 673, 1669, 10957] ⟨590750774833, 10, [(2, 4), (3, 1), (673, 1), (1669, 1), (10957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_673
    · exact prime_1669
    · exact prime_10957
  · decide +kernel

theorem prime_591663498577 : Nat.Prime 591663498577 := by
  apply nodeValid_prime [2, 3, 61, 202070867] ⟨591663498577, 5, [(2, 4), (3, 1), (61, 1), (202070867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_202070867
  · decide +kernel

theorem prime_591663499061 : Nat.Prime 591663499061 := by
  apply nodeValid_prime [2, 5, 37, 131, 373, 16363] ⟨591663499061, 2, [(2, 2), (5, 1), (37, 1), (131, 1), (373, 1), (16363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_131
    · exact prime_373
    · exact prime_16363
  · decide +kernel

theorem prime_591663500303 : Nat.Prime 591663500303 := by
  apply nodeValid_prime [2, 7, 42261678593] ⟨591663500303, 5, [(2, 1), (7, 1), (42261678593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_42261678593
  · decide +kernel

theorem prime_592577144849 : Nat.Prime 592577144849 := by
  apply nodeValid_prime [2, 13, 2848928581] ⟨592577144849, 3, [(2, 4), (13, 1), (2848928581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2848928581
  · decide +kernel

theorem prime_592577145253 : Nat.Prime 592577145253 := by
  apply nodeValid_prime [2, 3, 59, 347, 268003] ⟨592577145253, 14, [(2, 2), (3, 3), (59, 1), (347, 1), (268003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_347
    · exact prime_268003
  · decide +kernel

theorem prime_592577179979 : Nat.Prime 592577179979 := by
  apply nodeValid_prime [2, 7, 42326941427] ⟨592577179979, 2, [(2, 1), (7, 1), (42326941427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_42326941427
  · decide +kernel

theorem prime_593491778041 : Nat.Prime 593491778041 := by
  apply nodeValid_prime [2, 3, 5, 7, 706537831] ⟨593491778041, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (706537831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_706537831
  · decide +kernel

theorem prime_593491778521 : Nat.Prime 593491778521 := by
  apply nodeValid_prime [2, 3, 5, 2293, 2156897] ⟨593491778521, 7, [(2, 3), (3, 1), (5, 1), (2293, 1), (2156897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2293
    · exact prime_2156897
  · decide +kernel

theorem prime_593491816549 : Nat.Prime 593491816549 := by
  apply nodeValid_prime [2, 3, 31, 531802703] ⟨593491816549, 6, [(2, 2), (3, 2), (31, 1), (531802703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_531802703
  · decide +kernel

theorem prime_594407406409 : Nat.Prime 594407406409 := by
  apply nodeValid_prime [2, 3, 43, 631, 912799] ⟨594407406409, 7, [(2, 3), (3, 1), (43, 1), (631, 1), (912799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_631
    · exact prime_912799
  · decide +kernel

theorem prime_594407407813 : Nat.Prime 594407407813 := by
  apply nodeValid_prime [2, 3, 17, 37, 2128387] ⟨594407407813, 6, [(2, 2), (3, 1), (17, 1), (37, 2), (2128387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_2128387
  · decide +kernel

theorem prime_594407410567 : Nat.Prime 594407410567 := by
  apply nodeValid_prime [2, 3, 17, 59, 98771587] ⟨594407410567, 5, [(2, 1), (3, 1), (17, 1), (59, 1), (98771587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_59
    · exact prime_98771587
  · decide +kernel

theorem prime_595323961541 : Nat.Prime 595323961541 := by
  apply nodeValid_prime [2, 5, 7, 11, 35143091] ⟨595323961541, 10, [(2, 2), (5, 1), (7, 1), (11, 2), (35143091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_35143091
  · decide +kernel

theorem prime_595323980651 : Nat.Prime 595323980651 := by
  apply nodeValid_prime [2, 5, 7, 24593, 69163] ⟨595323980651, 2, [(2, 1), (5, 2), (7, 1), (24593, 1), (69163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_24593
    · exact prime_69163
  · decide +kernel

theorem prime_595323981467 : Nat.Prime 595323981467 := by
  apply nodeValid_prime [2, 29, 59, 173969603] ⟨595323981467, 2, [(2, 1), (29, 1), (59, 1), (173969603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_59
    · exact prime_173969603
  · decide +kernel

end Sude.Lucas.Generated
