import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0092
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0108

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10889 : Nat.Prime 10889 := by
  apply nodeValid_prime [2, 1361] ⟨10889, 3, [(2, 3), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1361
  · decide +kernel

theorem prime_11273 : Nat.Prime 11273 := by
  apply nodeValid_prime [2, 1409] ⟨11273, 3, [(2, 3), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1409
  · decide +kernel

theorem prime_15391 : Nat.Prime 15391 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨15391, 12, [(2, 1), (3, 4), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_20063 : Nat.Prime 20063 := by
  apply nodeValid_prime [2, 7, 1433] ⟨20063, 5, [(2, 1), (7, 1), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1433
  · decide +kernel

theorem prime_20789 : Nat.Prime 20789 := by
  apply nodeValid_prime [2, 5197] ⟨20789, 2, [(2, 2), (5197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5197
  · decide +kernel

theorem prime_26879 : Nat.Prime 26879 := by
  apply nodeValid_prime [2, 89, 151] ⟨26879, 13, [(2, 1), (89, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_151
  · decide +kernel

theorem prime_35257 : Nat.Prime 35257 := by
  apply nodeValid_prime [2, 3, 13, 113] ⟨35257, 7, [(2, 3), (3, 1), (13, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_113
  · decide +kernel

theorem prime_37013 : Nat.Prime 37013 := by
  apply nodeValid_prime [2, 19, 487] ⟨37013, 2, [(2, 2), (19, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_487
  · decide +kernel

theorem prime_39313 : Nat.Prime 39313 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨39313, 10, [(2, 4), (3, 3), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_40127 : Nat.Prime 40127 := by
  apply nodeValid_prime [2, 20063] ⟨40127, 5, [(2, 1), (20063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20063
  · decide +kernel

theorem prime_42967 : Nat.Prime 42967 := by
  apply nodeValid_prime [2, 3, 7, 11, 31] ⟨42967, 3, [(2, 1), (3, 2), (7, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_51769 : Nat.Prime 51769 := by
  apply nodeValid_prime [2, 3, 719] ⟨51769, 19, [(2, 3), (3, 2), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
  · decide +kernel

theorem prime_52709 : Nat.Prime 52709 := by
  apply nodeValid_prime [2, 13177] ⟨52709, 2, [(2, 2), (13177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13177
  · decide +kernel

theorem prime_52901 : Nat.Prime 52901 := by
  apply nodeValid_prime [2, 5, 23] ⟨52901, 3, [(2, 2), (5, 2), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_69499 : Nat.Prime 69499 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨69499, 3, [(2, 1), (3, 5), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_74027 : Nat.Prime 74027 := by
  apply nodeValid_prime [2, 37013] ⟨74027, 2, [(2, 1), (37013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37013
  · decide +kernel

theorem prime_76283 : Nat.Prime 76283 := by
  apply nodeValid_prime [2, 43, 887] ⟨76283, 2, [(2, 1), (43, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_887
  · decide +kernel

theorem prime_92723 : Nat.Prime 92723 := by
  apply nodeValid_prime [2, 7, 37, 179] ⟨92723, 2, [(2, 1), (7, 1), (37, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_179
  · decide +kernel

theorem prime_109229 : Nat.Prime 109229 := by
  apply nodeValid_prime [2, 7, 47, 83] ⟨109229, 2, [(2, 2), (7, 1), (47, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_83
  · decide +kernel

theorem prime_116411 : Nat.Prime 116411 := by
  apply nodeValid_prime [2, 5, 7, 1663] ⟨116411, 2, [(2, 1), (5, 1), (7, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1663
  · decide +kernel

theorem prime_117917 : Nat.Prime 117917 := by
  apply nodeValid_prime [2, 41, 719] ⟨117917, 2, [(2, 2), (41, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_719
  · decide +kernel

theorem prime_122609 : Nat.Prime 122609 := by
  apply nodeValid_prime [2, 79, 97] ⟨122609, 3, [(2, 4), (79, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_97
  · decide +kernel

theorem prime_152567 : Nat.Prime 152567 := by
  apply nodeValid_prime [2, 76283] ⟨152567, 5, [(2, 1), (76283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76283
  · decide +kernel

theorem prime_157253 : Nat.Prime 157253 := by
  apply nodeValid_prime [2, 39313] ⟨157253, 2, [(2, 2), (39313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39313
  · decide +kernel

theorem prime_166303 : Nat.Prime 166303 := by
  apply nodeValid_prime [2, 3, 9239] ⟨166303, 7, [(2, 1), (3, 2), (9239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9239
  · decide +kernel

theorem prime_175757 : Nat.Prime 175757 := by
  apply nodeValid_prime [2, 7, 6277] ⟨175757, 3, [(2, 2), (7, 1), (6277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6277
  · decide +kernel

theorem prime_196439 : Nat.Prime 196439 := by
  apply nodeValid_prime [2, 11, 8929] ⟨196439, 11, [(2, 1), (11, 1), (8929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8929
  · decide +kernel

theorem prime_218459 : Nat.Prime 218459 := by
  apply nodeValid_prime [2, 109229] ⟨218459, 2, [(2, 1), (109229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_109229
  · decide +kernel

theorem prime_303619 : Nat.Prime 303619 := by
  apply nodeValid_prime [2, 3, 7, 7229] ⟨303619, 2, [(2, 1), (3, 1), (7, 1), (7229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7229
  · decide +kernel

theorem prime_324089 : Nat.Prime 324089 := by
  apply nodeValid_prime [2, 17, 2383] ⟨324089, 3, [(2, 3), (17, 1), (2383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2383
  · decide +kernel

theorem prime_331153 : Nat.Prime 331153 := by
  apply nodeValid_prime [2, 3, 6899] ⟨331153, 5, [(2, 4), (3, 1), (6899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6899
  · decide +kernel

theorem prime_349043 : Nat.Prime 349043 := by
  apply nodeValid_prime [2, 61, 2861] ⟨349043, 2, [(2, 1), (61, 1), (2861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_2861
  · decide +kernel

theorem prime_368077 : Nat.Prime 368077 := by
  apply nodeValid_prime [2, 3, 37, 829] ⟨368077, 2, [(2, 2), (3, 1), (37, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_829
  · decide +kernel

theorem prime_441751 : Nat.Prime 441751 := by
  apply nodeValid_prime [2, 3, 5, 19, 31] ⟨441751, 6, [(2, 1), (3, 1), (5, 3), (19, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_31
  · decide +kernel

theorem prime_516599 : Nat.Prime 516599 := by
  apply nodeValid_prime [2, 258299] ⟨516599, 13, [(2, 1), (258299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_258299
  · decide +kernel

theorem prime_552301 : Nat.Prime 552301 := by
  apply nodeValid_prime [2, 3, 5, 7, 263] ⟨552301, 6, [(2, 2), (3, 1), (5, 2), (7, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_263
  · decide +kernel

theorem prime_564463 : Nat.Prime 564463 := by
  apply nodeValid_prime [2, 3, 10453] ⟨564463, 5, [(2, 1), (3, 3), (10453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10453
  · decide +kernel

theorem prime_592217 : Nat.Prime 592217 := by
  apply nodeValid_prime [2, 74027] ⟨592217, 3, [(2, 3), (74027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_74027
  · decide +kernel

theorem prime_616829 : Nat.Prime 616829 := by
  apply nodeValid_prime [2, 17, 47, 193] ⟨616829, 2, [(2, 2), (17, 1), (47, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_193
  · decide +kernel

theorem prime_643453 : Nat.Prime 643453 := by
  apply nodeValid_prime [2, 3, 29, 43] ⟨643453, 2, [(2, 2), (3, 1), (29, 1), (43, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_698273 : Nat.Prime 698273 := by
  apply nodeValid_prime [2, 21821] ⟨698273, 3, [(2, 5), (21821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21821
  · decide +kernel

theorem prime_716161 : Nat.Prime 716161 := by
  apply nodeValid_prime [2, 3, 5, 373] ⟨716161, 11, [(2, 7), (3, 1), (5, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_373
  · decide +kernel

theorem prime_912871 : Nat.Prime 912871 := by
  apply nodeValid_prime [2, 3, 5, 7, 23] ⟨912871, 6, [(2, 1), (3, 4), (5, 1), (7, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_961957 : Nat.Prime 961957 := by
  apply nodeValid_prime [2, 3, 2969] ⟨961957, 2, [(2, 2), (3, 4), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2969
  · decide +kernel

theorem prime_1044193 : Nat.Prime 1044193 := by
  apply nodeValid_prime [2, 3, 73, 149] ⟨1044193, 5, [(2, 5), (3, 1), (73, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_149
  · decide +kernel

theorem prime_1324613 : Nat.Prime 1324613 := by
  apply nodeValid_prime [2, 331153] ⟨1324613, 2, [(2, 2), (331153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_331153
  · decide +kernel

theorem prime_1396547 : Nat.Prime 1396547 := by
  apply nodeValid_prime [2, 698273] ⟨1396547, 2, [(2, 1), (698273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_698273
  · decide +kernel

theorem prime_1785367 : Nat.Prime 1785367 := by
  apply nodeValid_prime [2, 3, 11, 71, 127] ⟨1785367, 5, [(2, 1), (3, 2), (11, 1), (71, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_71
    · exact prime_127
  · decide +kernel

theorem prime_3841807 : Nat.Prime 3841807 := by
  apply nodeValid_prime [2, 3, 251, 2551] ⟨3841807, 3, [(2, 1), (3, 1), (251, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_2551
  · decide +kernel

theorem prime_3847829 : Nat.Prime 3847829 := by
  apply nodeValid_prime [2, 961957] ⟨3847829, 2, [(2, 2), (961957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_961957
  · decide +kernel

theorem prime_5255059 : Nat.Prime 5255059 := by
  apply nodeValid_prime [2, 3, 19, 31, 1487] ⟨5255059, 2, [(2, 1), (3, 1), (19, 1), (31, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_1487
  · decide +kernel

theorem prime_5906753 : Nat.Prime 5906753 := by
  apply nodeValid_prime [2, 17, 61, 89] ⟨5906753, 3, [(2, 6), (17, 1), (61, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_89
  · decide +kernel

theorem prime_7401949 : Nat.Prime 7401949 := by
  apply nodeValid_prime [2, 3, 616829] ⟨7401949, 6, [(2, 2), (3, 1), (616829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_616829
  · decide +kernel

theorem prime_7710733 : Nat.Prime 7710733 := by
  apply nodeValid_prime [2, 3, 19, 11273] ⟨7710733, 6, [(2, 2), (3, 2), (19, 1), (11273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11273
  · decide +kernel

theorem prime_8238619 : Nat.Prime 8238619 := by
  apply nodeValid_prime [2, 3, 152567] ⟨8238619, 2, [(2, 1), (3, 3), (152567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152567
  · decide +kernel

theorem prime_8432201 : Nat.Prime 8432201 := by
  apply nodeValid_prime [2, 5, 7, 19, 317] ⟨8432201, 3, [(2, 3), (5, 2), (7, 1), (19, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_317
  · decide +kernel

theorem prime_8593933 : Nat.Prime 8593933 := by
  apply nodeValid_prime [2, 3, 716161] ⟨8593933, 2, [(2, 2), (3, 1), (716161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_716161
  · decide +kernel

theorem prime_11252533 : Nat.Prime 11252533 := by
  apply nodeValid_prime [2, 3, 41, 22871] ⟨11252533, 2, [(2, 2), (3, 1), (41, 1), (22871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_22871
  · decide +kernel

theorem prime_12470009 : Nat.Prime 12470009 := by
  apply nodeValid_prime [2, 191, 8161] ⟨12470009, 3, [(2, 3), (191, 1), (8161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_8161
  · decide +kernel

theorem prime_12970871 : Nat.Prime 12970871 := by
  apply nodeValid_prime [2, 5, 11, 117917] ⟨12970871, 7, [(2, 1), (5, 1), (11, 1), (117917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_117917
  · decide +kernel

theorem prime_14213209 : Nat.Prime 14213209 := by
  apply nodeValid_prime [2, 3, 592217] ⟨14213209, 7, [(2, 3), (3, 1), (592217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_592217
  · decide +kernel

theorem prime_14909473 : Nat.Prime 14909473 := by
  apply nodeValid_prime [2, 3, 51769] ⟨14909473, 11, [(2, 5), (3, 2), (51769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51769
  · decide +kernel

theorem prime_20514023 : Nat.Prime 20514023 := by
  apply nodeValid_prime [2, 23, 41, 73, 149] ⟨20514023, 5, [(2, 1), (23, 1), (41, 1), (73, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_41
    · exact prime_73
    · exact prime_149
  · decide +kernel

theorem prime_24605981 : Nat.Prime 24605981 := by
  apply nodeValid_prime [2, 5, 7, 175757] ⟨24605981, 2, [(2, 2), (5, 1), (7, 1), (175757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_175757
  · decide +kernel

theorem prime_29135719 : Nat.Prime 29135719 := by
  apply nodeValid_prime [2, 3, 233, 6947] ⟨29135719, 3, [(2, 1), (3, 2), (233, 1), (6947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_6947
  · decide +kernel

theorem prime_33337637 : Nat.Prime 33337637 := by
  apply nodeValid_prime [2, 53, 157253] ⟨33337637, 2, [(2, 2), (53, 1), (157253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_157253
  · decide +kernel

theorem prime_37926491 : Nat.Prime 37926491 := by
  apply nodeValid_prime [2, 5, 7, 17, 29, 157] ⟨37926491, 2, [(2, 1), (5, 1), (7, 2), (17, 1), (29, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_29
    · exact prime_157
  · decide +kernel

theorem prime_41767721 : Nat.Prime 41767721 := by
  apply nodeValid_prime [2, 5, 1044193] ⟨41767721, 3, [(2, 3), (5, 1), (1044193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1044193
  · decide +kernel

theorem prime_49211963 : Nat.Prime 49211963 := by
  apply nodeValid_prime [2, 24605981] ⟨49211963, 2, [(2, 1), (24605981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24605981
  · decide +kernel

theorem prime_67457609 : Nat.Prime 67457609 := by
  apply nodeValid_prime [2, 8432201] ⟨67457609, 3, [(2, 3), (8432201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8432201
  · decide +kernel

theorem prime_86105869 : Nat.Prime 86105869 := by
  apply nodeValid_prime [2, 3, 167, 42967] ⟨86105869, 7, [(2, 2), (3, 1), (167, 1), (42967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_42967
  · decide +kernel

theorem prime_115479713 : Nat.Prime 115479713 := by
  apply nodeValid_prime [2, 31, 116411] ⟨115479713, 3, [(2, 5), (31, 1), (116411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_116411
  · decide +kernel

theorem prime_116298361 : Nat.Prime 116298361 := by
  apply nodeValid_prime [2, 3, 5, 17, 31, 613] ⟨116298361, 59, [(2, 3), (3, 2), (5, 1), (17, 1), (31, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_613
  · decide +kernel

theorem prime_117379807 : Nat.Prime 117379807 := by
  apply nodeValid_prime [2, 3, 2003, 9767] ⟨117379807, 3, [(2, 1), (3, 1), (2003, 1), (9767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2003
    · exact prime_9767
  · decide +kernel

theorem prime_124524739 : Nat.Prime 124524739 := by
  apply nodeValid_prime [2, 3, 13, 433, 1229] ⟨124524739, 2, [(2, 1), (3, 2), (13, 1), (433, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_433
    · exact prime_1229
  · decide +kernel

theorem prime_141950983 : Nat.Prime 141950983 := by
  apply nodeValid_prime [2, 3, 73, 324089] ⟨141950983, 3, [(2, 1), (3, 1), (73, 1), (324089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_324089
  · decide +kernel

theorem prime_197758937 : Nat.Prime 197758937 := by
  apply nodeValid_prime [2, 953, 25939] ⟨197758937, 3, [(2, 3), (953, 1), (25939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_953
    · exact prime_25939
  · decide +kernel

theorem prime_222215813 : Nat.Prime 222215813 := by
  apply nodeValid_prime [2, 7, 13, 31, 47, 419] ⟨222215813, 3, [(2, 2), (7, 1), (13, 1), (31, 1), (47, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_47
    · exact prime_419
  · decide +kernel

theorem prime_303004067 : Nat.Prime 303004067 := by
  apply nodeValid_prime [2, 911, 166303] ⟨303004067, 2, [(2, 1), (911, 1), (166303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_911
    · exact prime_166303
  · decide +kernel

theorem prime_317709839 : Nat.Prime 317709839 := by
  apply nodeValid_prime [2, 17, 61, 9011] ⟨317709839, 13, [(2, 1), (17, 2), (61, 1), (9011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_9011
  · decide +kernel

theorem prime_372028589 : Nat.Prime 372028589 := by
  apply nodeValid_prime [2, 19, 23, 29, 41, 179] ⟨372028589, 2, [(2, 2), (19, 1), (23, 1), (29, 1), (41, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_29
    · exact prime_41
    · exact prime_179
  · decide +kernel

theorem prime_496421839 : Nat.Prime 496421839 := by
  apply nodeValid_prime [2, 3, 11, 83, 10069] ⟨496421839, 3, [(2, 1), (3, 3), (11, 1), (83, 1), (10069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
    · exact prime_10069
  · decide +kernel

theorem prime_522485753 : Nat.Prime 522485753 := by
  apply nodeValid_prime [2, 17, 3841807] ⟨522485753, 3, [(2, 3), (17, 1), (3841807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3841807
  · decide +kernel

theorem prime_523056067 : Nat.Prime 523056067 := by
  apply nodeValid_prime [2, 3, 13, 643, 10429] ⟨523056067, 2, [(2, 1), (3, 1), (13, 1), (643, 1), (10429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_643
    · exact prime_10429
  · decide +kernel

theorem prime_531908309 : Nat.Prime 531908309 := by
  apply nodeValid_prime [2, 17, 379, 20639] ⟨531908309, 2, [(2, 2), (17, 1), (379, 1), (20639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_379
    · exact prime_20639
  · decide +kernel

theorem prime_562059713 : Nat.Prime 562059713 := by
  apply nodeValid_prime [2, 17, 516599] ⟨562059713, 3, [(2, 6), (17, 1), (516599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_516599
  · decide +kernel

theorem prime_601936781 : Nat.Prime 601936781 := by
  apply nodeValid_prime [2, 5, 571, 52709] ⟨601936781, 2, [(2, 2), (5, 1), (571, 1), (52709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_571
    · exact prime_52709
  · decide +kernel

theorem prime_617795293 : Nat.Prime 617795293 := by
  apply nodeValid_prime [2, 3, 1283, 40127] ⟨617795293, 2, [(2, 2), (3, 1), (1283, 1), (40127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1283
    · exact prime_40127
  · decide +kernel

theorem prime_646273489 : Nat.Prime 646273489 := by
  apply nodeValid_prime [2, 3, 7, 41, 43, 1091] ⟨646273489, 34, [(2, 4), (3, 1), (7, 1), (41, 1), (43, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_43
    · exact prime_1091
  · decide +kernel

theorem prime_674101123 : Nat.Prime 674101123 := by
  apply nodeValid_prime [2, 3, 71, 1039, 1523] ⟨674101123, 3, [(2, 1), (3, 1), (71, 1), (1039, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_1039
    · exact prime_1523
  · decide +kernel

theorem prime_798184591 : Nat.Prime 798184591 := by
  apply nodeValid_prime [2, 3, 5, 7, 31, 122609] ⟨798184591, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (122609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_122609
  · decide +kernel

theorem prime_837571807 : Nat.Prime 837571807 := by
  apply nodeValid_prime [2, 3, 71, 218459] ⟨837571807, 3, [(2, 1), (3, 3), (71, 1), (218459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_218459
  · decide +kernel

theorem prime_890180411 : Nat.Prime 890180411 := by
  apply nodeValid_prime [2, 5, 7, 37, 43, 7993] ⟨890180411, 7, [(2, 1), (5, 1), (7, 1), (37, 1), (43, 1), (7993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_43
    · exact prime_7993
  · decide +kernel

theorem prime_922707707 : Nat.Prime 922707707 := by
  apply nodeValid_prime [2, 41, 11252533] ⟨922707707, 2, [(2, 1), (41, 1), (11252533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_11252533
  · decide +kernel

theorem prime_959954557 : Nat.Prime 959954557 := by
  apply nodeValid_prime [2, 3, 11, 19, 31, 12347] ⟨959954557, 5, [(2, 2), (3, 1), (11, 1), (19, 1), (31, 1), (12347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_31
    · exact prime_12347
  · decide +kernel

theorem prime_1063816619 : Nat.Prime 1063816619 := by
  apply nodeValid_prime [2, 531908309] ⟨1063816619, 2, [(2, 1), (531908309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_531908309
  · decide +kernel

theorem prime_1443734839 : Nat.Prime 1443734839 := by
  apply nodeValid_prime [2, 3, 7, 13, 59, 14939] ⟨1443734839, 6, [(2, 1), (3, 2), (7, 1), (13, 1), (59, 1), (14939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_59
    · exact prime_14939
  · decide +kernel

theorem prime_2533492207 : Nat.Prime 2533492207 := by
  apply nodeValid_prime [2, 3, 7, 3433, 5857] ⟨2533492207, 6, [(2, 1), (3, 2), (7, 1), (3433, 1), (5857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3433
    · exact prime_5857
  · decide +kernel

theorem prime_2881671409 : Nat.Prime 2881671409 := by
  apply nodeValid_prime [2, 3, 7, 11, 293, 887] ⟨2881671409, 13, [(2, 4), (3, 2), (7, 1), (11, 1), (293, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_293
    · exact prime_887
  · decide +kernel

theorem prime_4476491623 : Nat.Prime 4476491623 := by
  apply nodeValid_prime [2, 3, 83, 661, 1511] ⟨4476491623, 5, [(2, 1), (3, 3), (83, 1), (661, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_661
    · exact prime_1511
  · decide +kernel

theorem prime_7582753603 : Nat.Prime 7582753603 := by
  apply nodeValid_prime [2, 3, 3373, 13877] ⟨7582753603, 2, [(2, 1), (3, 4), (3373, 1), (13877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3373
    · exact prime_13877
  · decide +kernel

theorem prime_25127154211 : Nat.Prime 25127154211 := by
  apply nodeValid_prime [2, 3, 5, 837571807] ⟨25127154211, 3, [(2, 1), (3, 1), (5, 1), (837571807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_837571807
  · decide +kernel

theorem prime_26878727597 : Nat.Prime 26878727597 := by
  apply nodeValid_prime [2, 7, 959954557] ⟨26878727597, 2, [(2, 2), (7, 1), (959954557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_959954557
  · decide +kernel

theorem prime_27381666343 : Nat.Prime 27381666343 := by
  apply nodeValid_prime [2, 3, 53, 86105869] ⟨27381666343, 3, [(2, 1), (3, 1), (53, 1), (86105869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_86105869
  · decide +kernel

theorem prime_59436866761 : Nat.Prime 59436866761 := by
  apply nodeValid_prime [2, 3, 5, 17, 29135719] ⟨59436866761, 7, [(2, 3), (3, 1), (5, 1), (17, 1), (29135719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_29135719
  · decide +kernel

theorem prime_92334346001 : Nat.Prime 92334346001 := by
  apply nodeValid_prime [2, 5, 13, 83, 42787] ⟨92334346001, 3, [(2, 4), (5, 3), (13, 1), (83, 1), (42787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_83
    · exact prime_42787
  · decide +kernel

theorem prime_172489681069 : Nat.Prime 172489681069 := by
  apply nodeValid_prime [2, 3, 379, 37926491] ⟨172489681069, 2, [(2, 2), (3, 1), (379, 1), (37926491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_37926491
  · decide +kernel

theorem prime_525045453553 : Nat.Prime 525045453553 := by
  apply nodeValid_prime [2, 3, 41, 8167, 10889] ⟨525045453553, 7, [(2, 4), (3, 2), (41, 1), (8167, 1), (10889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_8167
    · exact prime_10889
  · decide +kernel

theorem prime_655305515009 : Nat.Prime 655305515009 := by
  apply nodeValid_prime [2, 1151, 69499] ⟨655305515009, 3, [(2, 13), (1151, 1), (69499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1151
    · exact prime_69499
  · decide +kernel

theorem prime_863109883123 : Nat.Prime 863109883123 := by
  apply nodeValid_prime [2, 3, 131, 829, 1324613] ⟨863109883123, 2, [(2, 1), (3, 1), (131, 1), (829, 1), (1324613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_829
    · exact prime_1324613
  · decide +kernel

theorem prime_867086102327 : Nat.Prime 867086102327 := by
  apply nodeValid_prime [2, 1951, 222215813] ⟨867086102327, 5, [(2, 1), (1951, 1), (222215813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1951
    · exact prime_222215813
  · decide +kernel

theorem prime_875075745497 : Nat.Prime 875075745497 := by
  apply nodeValid_prime [2, 19, 303004067] ⟨875075745497, 5, [(2, 3), (19, 2), (303004067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_303004067
  · decide +kernel

theorem prime_1289708713177 : Nat.Prime 1289708713177 := by
  apply nodeValid_prime [2, 3, 13, 37, 8593933] ⟨1289708713177, 5, [(2, 3), (3, 1), (13, 2), (37, 1), (8593933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_8593933
  · decide +kernel

theorem prime_1290698946067 : Nat.Prime 1290698946067 := by
  apply nodeValid_prime [2, 3, 149, 1443734839] ⟨1290698946067, 2, [(2, 1), (3, 1), (149, 1), (1443734839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_1443734839
  · decide +kernel

theorem prime_1313615688079 : Nat.Prime 1313615688079 := by
  apply nodeValid_prime [2, 3, 97, 181, 12470009] ⟨1313615688079, 3, [(2, 1), (3, 1), (97, 1), (181, 1), (12470009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_181
    · exact prime_12470009
  · decide +kernel

theorem prime_2595289323551 : Nat.Prime 2595289323551 := by
  apply nodeValid_prime [2, 5, 7, 11, 674101123] ⟨2595289323551, 7, [(2, 1), (5, 2), (7, 1), (11, 1), (674101123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_674101123
  · decide +kernel

theorem prime_2623224091079 : Nat.Prime 2623224091079 := by
  apply nodeValid_prime [2, 293, 4476491623] ⟨2623224091079, 7, [(2, 1), (293, 1), (4476491623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_293
    · exact prime_4476491623
  · decide +kernel

theorem prime_5158834852621 : Nat.Prime 5158834852621 := by
  apply nodeValid_prime [2, 3, 5, 97, 971, 912871] ⟨5158834852621, 2, [(2, 2), (3, 1), (5, 1), (97, 1), (971, 1), (912871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_971
    · exact prime_912871
  · decide +kernel

theorem prime_5158834852709 : Nat.Prime 5158834852709 := by
  apply nodeValid_prime [2, 1289708713177] ⟨5158834852709, 2, [(2, 2), (1289708713177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1289708713177
  · decide +kernel

theorem prime_5158834913591 : Nat.Prime 5158834913591 := by
  apply nodeValid_prime [2, 5, 17, 47, 18313, 35257] ⟨5158834913591, 7, [(2, 1), (5, 1), (17, 1), (47, 1), (18313, 1), (35257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_47
    · exact prime_18313
    · exact prime_35257
  · decide +kernel

theorem prime_5162795678941 : Nat.Prime 5162795678941 := by
  apply nodeValid_prime [2, 3, 5, 691, 124524739] ⟨5162795678941, 2, [(2, 2), (3, 1), (5, 1), (691, 1), (124524739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_691
    · exact prime_124524739
  · decide +kernel

theorem prime_5162795784131 : Nat.Prime 5162795784131 := by
  apply nodeValid_prime [2, 5, 53, 751, 12970871] ⟨5162795784131, 2, [(2, 1), (5, 1), (53, 1), (751, 1), (12970871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_751
    · exact prime_12970871
  · decide +kernel

theorem prime_5162795784269 : Nat.Prime 5162795784269 := by
  apply nodeValid_prime [2, 1290698946067] ⟨5162795784269, 2, [(2, 2), (1290698946067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1290698946067
  · decide +kernel

theorem prime_5166758500313 : Nat.Prime 5166758500313 := by
  apply nodeValid_prime [2, 1301, 496421839] ⟨5166758500313, 3, [(2, 3), (1301, 1), (496421839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1301
    · exact prime_496421839
  · decide +kernel

theorem prime_5166758569867 : Nat.Prime 5166758569867 := by
  apply nodeValid_prime [2, 3, 17, 31, 239, 709, 9643] ⟨5166758569867, 5, [(2, 1), (3, 1), (17, 1), (31, 1), (239, 1), (709, 1), (9643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_239
    · exact prime_709
    · exact prime_9643
  · decide +kernel

theorem prime_5166758570089 : Nat.Prime 5166758570089 := by
  apply nodeValid_prime [2, 3, 311, 1567, 441751] ⟨5166758570089, 11, [(2, 3), (3, 1), (311, 1), (1567, 1), (441751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_1567
    · exact prime_441751
  · decide +kernel

theorem prime_5170723376057 : Nat.Prime 5170723376057 := by
  apply nodeValid_prime [2, 7, 92334346001] ⟨5170723376057, 3, [(2, 3), (7, 1), (92334346001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_92334346001
  · decide +kernel

theorem prime_5170723501103 : Nat.Prime 5170723501103 := by
  apply nodeValid_prime [2, 113, 227, 1087, 92723] ⟨5170723501103, 5, [(2, 1), (113, 1), (227, 1), (1087, 1), (92723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_227
    · exact prime_1087
    · exact prime_92723
  · decide +kernel

theorem prime_5170723501871 : Nat.Prime 5170723501871 := by
  apply nodeValid_prime [2, 5, 53, 131, 4447, 16747] ⟨5170723501871, 7, [(2, 1), (5, 1), (53, 1), (131, 1), (4447, 1), (16747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_131
    · exact prime_4447
    · exact prime_16747
  · decide +kernel

theorem prime_5174690308789 : Nat.Prime 5174690308789 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 47, 79, 157, 739] ⟨5174690308789, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (47, 1), (79, 1), (157, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_47
    · exact prime_79
    · exact prime_157
    · exact prime_739
  · decide +kernel

theorem prime_5174690432003 : Nat.Prime 5174690432003 := by
  apply nodeValid_prime [2, 7, 13, 1907, 14909473] ⟨5174690432003, 2, [(2, 1), (7, 1), (13, 1), (1907, 1), (14909473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1907
    · exact prime_14909473
  · decide +kernel

theorem prime_5174690432071 : Nat.Prime 5174690432071 := by
  apply nodeValid_prime [2, 3, 5, 172489681069] ⟨5174690432071, 15, [(2, 1), (3, 1), (5, 1), (172489681069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_172489681069
  · decide +kernel

theorem prime_5178659298739 : Nat.Prime 5178659298739 := by
  apply nodeValid_prime [2, 3, 863109883123] ⟨5178659298739, 2, [(2, 1), (3, 1), (863109883123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863109883123
  · decide +kernel

theorem prime_5178659301293 : Nat.Prime 5178659301293 := by
  apply nodeValid_prime [2, 1217, 1063816619] ⟨5178659301293, 2, [(2, 2), (1217, 1), (1063816619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1217
    · exact prime_1063816619
  · decide +kernel

theorem prime_5178659301533 : Nat.Prime 5178659301533 := by
  apply nodeValid_prime [2, 41, 211, 8287, 18059] ⟨5178659301533, 2, [(2, 2), (41, 1), (211, 1), (8287, 1), (18059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_211
    · exact prime_8287
    · exact prime_18059
  · decide +kernel

theorem prime_5182630352843 : Nat.Prime 5182630352843 := by
  apply nodeValid_prime [2, 41, 71, 890180411] ⟨5182630352843, 2, [(2, 1), (41, 1), (71, 1), (890180411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_71
    · exact prime_890180411
  · decide +kernel

theorem prime_5182630389331 : Nat.Prime 5182630389331 := by
  apply nodeValid_prime [2, 3, 5, 1217, 141950983] ⟨5182630389331, 2, [(2, 1), (3, 1), (5, 1), (1217, 1), (141950983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1217
    · exact prime_141950983
  · decide +kernel

theorem prime_5182630392757 : Nat.Prime 5182630392757 := by
  apply nodeValid_prime [2, 3, 79, 709, 7710733] ⟨5182630392757, 5, [(2, 2), (3, 1), (79, 1), (709, 1), (7710733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_709
    · exact prime_7710733
  · decide +kernel

theorem prime_5186603460901 : Nat.Prime 5186603460901 := by
  apply nodeValid_prime [2, 3, 5, 23, 1361, 552301] ⟨5186603460901, 6, [(2, 2), (3, 1), (5, 2), (23, 1), (1361, 1), (552301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1361
    · exact prime_552301
  · decide +kernel

theorem prime_5186603464453 : Nat.Prime 5186603464453 := by
  apply nodeValid_prime [2, 3, 19, 7582753603] ⟨5186603464453, 2, [(2, 2), (3, 2), (19, 1), (7582753603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7582753603
  · decide +kernel

theorem prime_5186603472319 : Nat.Prime 5186603472319 := by
  apply nodeValid_prime [2, 3, 19, 798184591] ⟨5186603472319, 3, [(2, 1), (3, 2), (19, 2), (798184591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_798184591
  · decide +kernel

theorem prime_5190578647103 : Nat.Prime 5190578647103 := by
  apply nodeValid_prime [2, 2595289323551] ⟨5190578647103, 5, [(2, 1), (2595289323551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2595289323551
  · decide +kernel

theorem prime_5190578647547 : Nat.Prime 5190578647547 := by
  apply nodeValid_prime [2, 17, 23, 467, 14213209] ⟨5190578647547, 2, [(2, 1), (17, 1), (23, 1), (467, 1), (14213209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_467
    · exact prime_14213209
  · decide +kernel

theorem prime_5190578662099 : Nat.Prime 5190578662099 := by
  apply nodeValid_prime [2, 3, 17, 31, 4703, 349043] ⟨5190578662099, 2, [(2, 1), (3, 1), (17, 1), (31, 1), (4703, 1), (349043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_4703
    · exact prime_349043
  · decide +kernel

theorem prime_5194555867547 : Nat.Prime 5194555867547 := by
  apply nodeValid_prime [2, 4621, 562059713] ⟨5194555867547, 2, [(2, 1), (4621, 1), (562059713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4621
    · exact prime_562059713
  · decide +kernel

theorem prime_5194555867651 : Nat.Prime 5194555867651 := by
  apply nodeValid_prime [2, 3, 5, 109, 317709839] ⟨5194555867651, 2, [(2, 1), (3, 1), (5, 2), (109, 1), (317709839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_317709839
  · decide +kernel

theorem prime_5194555911913 : Nat.Prime 5194555911913 := by
  apply nodeValid_prime [2, 3, 53, 20789, 196439] ⟨5194555911913, 5, [(2, 3), (3, 1), (53, 1), (20789, 1), (196439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_20789
    · exact prime_196439
  · decide +kernel

theorem prime_5198535220783 : Nat.Prime 5198535220783 := by
  apply nodeValid_prime [2, 3, 97, 5003, 1785367] ⟨5198535220783, 3, [(2, 1), (3, 1), (97, 1), (5003, 1), (1785367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_5003
    · exact prime_1785367
  · decide +kernel

theorem prime_5198535221239 : Nat.Prime 5198535221239 := by
  apply nodeValid_prime [2, 3, 313, 922707707] ⟨5198535221239, 15, [(2, 1), (3, 2), (313, 1), (922707707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
    · exact prime_922707707
  · decide +kernel

theorem prime_5198535221837 : Nat.Prime 5198535221837 := by
  apply nodeValid_prime [2, 11, 41, 2881671409] ⟨5198535221837, 2, [(2, 2), (11, 1), (41, 1), (2881671409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_2881671409
  · decide +kernel

theorem prime_5202516605171 : Nat.Prime 5202516605171 := by
  apply nodeValid_prime [2, 5, 19, 27381666343] ⟨5202516605171, 2, [(2, 1), (5, 1), (19, 1), (27381666343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_27381666343
  · decide +kernel

theorem prime_5202516613103 : Nat.Prime 5202516613103 := by
  apply nodeValid_prime [2, 17, 307, 883, 564463] ⟨5202516613103, 5, [(2, 1), (17, 1), (307, 1), (883, 1), (564463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_307
    · exact prime_883
    · exact prime_564463
  · decide +kernel

theorem prime_5202516613963 : Nat.Prime 5202516613963 := by
  apply nodeValid_prime [2, 3, 867086102327] ⟨5202516613963, 7, [(2, 1), (3, 1), (867086102327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_867086102327
  · decide +kernel

theorem prime_5206500065447 : Nat.Prime 5206500065447 := by
  apply nodeValid_prime [2, 19, 6679, 20514023] ⟨5206500065447, 5, [(2, 1), (19, 1), (6679, 1), (20514023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_6679
    · exact prime_20514023
  · decide +kernel

theorem prime_5206500090751 : Nat.Prime 5206500090751 := by
  apply nodeValid_prime [2, 3, 5, 7, 59, 167, 251, 401] ⟨5206500090751, 3, [(2, 1), (3, 1), (5, 3), (7, 1), (59, 1), (167, 1), (251, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_167
    · exact prime_251
    · exact prime_401
  · decide +kernel

theorem prime_5206500090919 : Nat.Prime 5206500090919 := by
  apply nodeValid_prime [2, 3, 7, 79, 523056067] ⟨5206500090919, 3, [(2, 1), (3, 2), (7, 1), (79, 1), (523056067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_523056067
  · decide +kernel

theorem prime_5210485497383 : Nat.Prime 5210485497383 := by
  apply nodeValid_prime [2, 11, 368077, 643453] ⟨5210485497383, 5, [(2, 1), (11, 1), (368077, 1), (643453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_368077
    · exact prime_643453
  · decide +kernel

theorem prime_5210485501163 : Nat.Prime 5210485501163 := by
  apply nodeValid_prime [2, 4217, 617795293] ⟨5210485501163, 2, [(2, 1), (4217, 1), (617795293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4217
    · exact prime_617795293
  · decide +kernel

theorem prime_5210485589563 : Nat.Prime 5210485589563 := by
  apply nodeValid_prime [2, 3, 11, 83, 181, 5255059] ⟨5210485589563, 5, [(2, 1), (3, 1), (11, 1), (83, 1), (181, 1), (5255059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
    · exact prime_181
    · exact prime_5255059
  · decide +kernel

theorem prime_5214473153719 : Nat.Prime 5214473153719 := by
  apply nodeValid_prime [2, 3, 131, 199, 33337637] ⟨5214473153719, 6, [(2, 1), (3, 1), (131, 1), (199, 1), (33337637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_199
    · exact prime_33337637
  · decide +kernel

theorem prime_5214473153819 : Nat.Prime 5214473153819 := by
  apply nodeValid_prime [2, 97, 26878727597] ⟨5214473153819, 2, [(2, 1), (97, 1), (26878727597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_26878727597
  · decide +kernel

theorem prime_5214473175701 : Nat.Prime 5214473175701 := by
  apply nodeValid_prime [2, 5, 773, 67457609] ⟨5214473175701, 2, [(2, 2), (5, 2), (773, 1), (67457609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_773
    · exact prime_67457609
  · decide +kernel

theorem prime_5218462829557 : Nat.Prime 5218462829557 := by
  apply nodeValid_prime [2, 3, 733, 197758937] ⟨5218462829557, 2, [(2, 2), (3, 2), (733, 1), (197758937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_733
    · exact prime_197758937
  · decide +kernel

theorem prime_5218462868389 : Nat.Prime 5218462868389 := by
  apply nodeValid_prime [2, 3, 7, 11, 109, 7401949] ⟨5218462868389, 2, [(2, 2), (3, 1), (7, 2), (11, 1), (109, 1), (7401949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_109
    · exact prime_7401949
  · decide +kernel

theorem prime_5218462868587 : Nat.Prime 5218462868587 := by
  apply nodeValid_prime [2, 3, 11, 569, 10253, 13553] ⟨5218462868587, 2, [(2, 1), (3, 1), (11, 1), (569, 1), (10253, 1), (13553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_569
    · exact prime_10253
    · exact prime_13553
  · decide +kernel

theorem prime_5222454540713 : Nat.Prime 5222454540713 := by
  apply nodeValid_prime [2, 5653, 115479713] ⟨5222454540713, 3, [(2, 3), (5653, 1), (115479713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5653
    · exact prime_115479713
  · decide +kernel

theorem prime_5222454540757 : Nat.Prime 5222454540757 := by
  apply nodeValid_prime [2, 3, 281, 1109, 1396547] ⟨5222454540757, 2, [(2, 2), (3, 1), (281, 1), (1109, 1), (1396547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_1109
    · exact prime_1396547
  · decide +kernel

theorem prime_5222454552389 : Nat.Prime 5222454552389 := by
  apply nodeValid_prime [2, 17, 233, 12263, 26879] ⟨5222454552389, 2, [(2, 2), (17, 1), (233, 1), (12263, 1), (26879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_233
    · exact prime_12263
    · exact prime_26879
  · decide +kernel

theorem prime_5226448075697 : Nat.Prime 5226448075697 := by
  apply nodeValid_prime [2, 31, 1279, 8238619] ⟨5226448075697, 3, [(2, 4), (31, 1), (1279, 1), (8238619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1279
    · exact prime_8238619
  · decide +kernel

theorem prime_5226448075889 : Nat.Prime 5226448075889 := by
  apply nodeValid_prime [2, 13, 25127154211] ⟨5226448075889, 3, [(2, 4), (13, 1), (25127154211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_25127154211
  · decide +kernel

theorem prime_5226448343341 : Nat.Prime 5226448343341 := by
  apply nodeValid_prime [2, 3, 5, 7, 107, 116298361] ⟨5226448343341, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (107, 1), (116298361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_107
    · exact prime_116298361
  · decide +kernel

theorem prime_5230444199921 : Nat.Prime 5230444199921 := by
  apply nodeValid_prime [2, 5, 557, 117379807] ⟨5230444199921, 3, [(2, 4), (5, 1), (557, 1), (117379807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_557
    · exact prime_117379807
  · decide +kernel

theorem prime_5230444274969 : Nat.Prime 5230444274969 := by
  apply nodeValid_prime [2, 11, 59436866761] ⟨5230444274969, 3, [(2, 3), (11, 1), (59436866761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59436866761
  · decide +kernel

theorem prime_5230444275493 : Nat.Prime 5230444275493 := by
  apply nodeValid_prime [2, 3, 17, 521, 49211963] ⟨5230444275493, 2, [(2, 2), (3, 1), (17, 1), (521, 1), (49211963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_521
    · exact prime_49211963
  · decide +kernel

theorem prime_5234442117287 : Nat.Prime 5234442117287 := by
  apply nodeValid_prime [2, 23, 89, 24169, 52901] ⟨5234442117287, 10, [(2, 1), (23, 1), (89, 1), (24169, 1), (52901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_89
    · exact prime_24169
    · exact prime_52901
  · decide +kernel

theorem prime_5234442247231 : Nat.Prime 5234442247231 := by
  apply nodeValid_prime [2, 3, 5, 7, 67, 372028589] ⟨5234442247231, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (67, 1), (372028589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_67
    · exact prime_372028589
  · decide +kernel

theorem prime_5234442247577 : Nat.Prime 5234442247577 := by
  apply nodeValid_prime [2, 1087, 601936781] ⟨5234442247577, 3, [(2, 3), (1087, 1), (601936781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1087
    · exact prime_601936781
  · decide +kernel

theorem prime_5238442096259 : Nat.Prime 5238442096259 := by
  apply nodeValid_prime [2, 7, 47, 2069, 3847829] ⟨5238442096259, 2, [(2, 1), (7, 1), (47, 1), (2069, 1), (3847829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_2069
    · exact prime_3847829
  · decide +kernel

theorem prime_5238442159373 : Nat.Prime 5238442159373 := by
  apply nodeValid_prime [2, 3463, 15391, 24571] ⟨5238442159373, 2, [(2, 2), (3463, 1), (15391, 1), (24571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3463
    · exact prime_15391
    · exact prime_24571
  · decide +kernel

theorem prime_5238442159579 : Nat.Prime 5238442159579 := by
  apply nodeValid_prime [2, 3, 557, 522485753] ⟨5238442159579, 3, [(2, 1), (3, 2), (557, 1), (522485753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_557
    · exact prime_522485753
  · decide +kernel

theorem prime_5242444117103 : Nat.Prime 5242444117103 := by
  apply nodeValid_prime [2, 73, 6079, 5906753] ⟨5242444117103, 5, [(2, 1), (73, 1), (6079, 1), (5906753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_6079
    · exact prime_5906753
  · decide +kernel

theorem prime_5242444120073 : Nat.Prime 5242444120073 := by
  apply nodeValid_prime [2, 655305515009] ⟨5242444120073, 3, [(2, 3), (655305515009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_655305515009
  · decide +kernel

theorem prime_5242444143119 : Nat.Prime 5242444143119 := by
  apply nodeValid_prime [2, 7, 13, 13553, 303619] ⟨5242444143119, 7, [(2, 1), (7, 2), (13, 1), (13553, 1), (303619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_13553
    · exact prime_303619
  · decide +kernel

theorem prime_5246448182159 : Nat.Prime 5246448182159 := by
  apply nodeValid_prime [2, 2623224091079] ⟨5246448182159, 7, [(2, 1), (2623224091079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2623224091079
  · decide +kernel

theorem prime_5246448183703 : Nat.Prime 5246448183703 := by
  apply nodeValid_prime [2, 3, 11, 41, 646273489] ⟨5246448183703, 10, [(2, 1), (3, 2), (11, 1), (41, 1), (646273489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_646273489
  · decide +kernel

theorem prime_5246448267839 : Nat.Prime 5246448267839 := by
  apply nodeValid_prime [2, 19, 89, 389, 1471, 2711] ⟨5246448267839, 7, [(2, 1), (19, 1), (89, 1), (389, 1), (1471, 1), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_89
    · exact prime_389
    · exact prime_1471
    · exact prime_2711
  · decide +kernel

theorem prime_5250454472983 : Nat.Prime 5250454472983 := by
  apply nodeValid_prime [2, 3, 875075745497] ⟨5250454472983, 3, [(2, 1), (3, 1), (875075745497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_875075745497
  · decide +kernel

theorem prime_5250454535111 : Nat.Prime 5250454535111 := by
  apply nodeValid_prime [2, 5, 41, 467, 5171, 5303] ⟨5250454535111, 7, [(2, 1), (5, 1), (41, 1), (467, 1), (5171, 1), (5303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_467
    · exact prime_5171
    · exact prime_5303
  · decide +kernel

theorem prime_5250454535531 : Nat.Prime 5250454535531 := by
  apply nodeValid_prime [2, 5, 525045453553] ⟨5250454535531, 6, [(2, 1), (5, 1), (525045453553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_525045453553
  · decide +kernel

theorem prime_5254462752317 : Nat.Prime 5254462752317 := by
  apply nodeValid_prime [2, 1313615688079] ⟨5254462752317, 2, [(2, 2), (1313615688079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1313615688079
  · decide +kernel

theorem prime_5254462837243 : Nat.Prime 5254462837243 := by
  apply nodeValid_prime [2, 3, 29, 241, 41767721] ⟨5254462837243, 3, [(2, 1), (3, 2), (29, 1), (241, 1), (41767721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_241
    · exact prime_41767721
  · decide +kernel

theorem prime_5254462837319 : Nat.Prime 5254462837319 := by
  apply nodeValid_prime [2, 17, 61, 2533492207] ⟨5254462837319, 11, [(2, 1), (17, 1), (61, 1), (2533492207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_2533492207
  · decide +kernel

end Sude.Lucas.Generated
