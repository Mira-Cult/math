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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0106
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0139

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_6961 : Nat.Prime 6961 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨6961, 13, [(2, 4), (3, 1), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_16741 : Nat.Prime 16741 := by
  apply nodeValid_prime [2, 3, 5, 31] ⟨16741, 6, [(2, 2), (3, 3), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_17929 : Nat.Prime 17929 := by
  apply nodeValid_prime [2, 3, 83] ⟨17929, 11, [(2, 3), (3, 3), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_19843 : Nat.Prime 19843 := by
  apply nodeValid_prime [2, 3, 3307] ⟨19843, 19, [(2, 1), (3, 1), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3307
  · decide +kernel

theorem prime_31147 : Nat.Prime 31147 := by
  apply nodeValid_prime [2, 3, 29, 179] ⟨31147, 2, [(2, 1), (3, 1), (29, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_179
  · decide +kernel

theorem prime_32173 : Nat.Prime 32173 := by
  apply nodeValid_prime [2, 3, 7, 383] ⟨32173, 5, [(2, 2), (3, 1), (7, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
  · decide +kernel

theorem prime_43207 : Nat.Prime 43207 := by
  apply nodeValid_prime [2, 3, 19, 379] ⟨43207, 3, [(2, 1), (3, 1), (19, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_379
  · decide +kernel

theorem prime_43331 : Nat.Prime 43331 := by
  apply nodeValid_prime [2, 5, 7, 619] ⟨43331, 2, [(2, 1), (5, 1), (7, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_619
  · decide +kernel

theorem prime_47699 : Nat.Prime 47699 := by
  apply nodeValid_prime [2, 7, 3407] ⟨47699, 2, [(2, 1), (7, 1), (3407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3407
  · decide +kernel

theorem prime_54941 : Nat.Prime 54941 := by
  apply nodeValid_prime [2, 5, 41, 67] ⟨54941, 2, [(2, 2), (5, 1), (41, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_67
  · decide +kernel

theorem prime_62483 : Nat.Prime 62483 := by
  apply nodeValid_prime [2, 7, 4463] ⟨62483, 2, [(2, 1), (7, 1), (4463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4463
  · decide +kernel

theorem prime_63377 : Nat.Prime 63377 := by
  apply nodeValid_prime [2, 17, 233] ⟨63377, 3, [(2, 4), (17, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_233
  · decide +kernel

theorem prime_65071 : Nat.Prime 65071 := by
  apply nodeValid_prime [2, 3, 5, 241] ⟨65071, 3, [(2, 1), (3, 3), (5, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_66809 : Nat.Prime 66809 := by
  apply nodeValid_prime [2, 7, 1193] ⟨66809, 6, [(2, 3), (7, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1193
  · decide +kernel

theorem prime_87559 : Nat.Prime 87559 := by
  apply nodeValid_prime [2, 3, 14593] ⟨87559, 3, [(2, 1), (3, 1), (14593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14593
  · decide +kernel

theorem prime_91129 : Nat.Prime 91129 := by
  apply nodeValid_prime [2, 3, 3797] ⟨91129, 7, [(2, 3), (3, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3797
  · decide +kernel

theorem prime_100447 : Nat.Prime 100447 := by
  apply nodeValid_prime [2, 3, 16741] ⟨100447, 3, [(2, 1), (3, 1), (16741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16741
  · decide +kernel

theorem prime_105727 : Nat.Prime 105727 := by
  apply nodeValid_prime [2, 3, 67, 263] ⟨105727, 6, [(2, 1), (3, 1), (67, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_263
  · decide +kernel

theorem prime_112759 : Nat.Prime 112759 := by
  apply nodeValid_prime [2, 3, 18793] ⟨112759, 3, [(2, 1), (3, 1), (18793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18793
  · decide +kernel

theorem prime_114281 : Nat.Prime 114281 := by
  apply nodeValid_prime [2, 5, 2857] ⟨114281, 6, [(2, 3), (5, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2857
  · decide +kernel

theorem prime_115771 : Nat.Prime 115771 := by
  apply nodeValid_prime [2, 3, 5, 17, 227] ⟨115771, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_227
  · decide +kernel

theorem prime_116989 : Nat.Prime 116989 := by
  apply nodeValid_prime [2, 3, 9749] ⟨116989, 10, [(2, 2), (3, 1), (9749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9749
  · decide +kernel

theorem prime_120997 : Nat.Prime 120997 := by
  apply nodeValid_prime [2, 3, 3361] ⟨120997, 2, [(2, 2), (3, 2), (3361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3361
  · decide +kernel

theorem prime_128693 : Nat.Prime 128693 := by
  apply nodeValid_prime [2, 32173] ⟨128693, 2, [(2, 2), (32173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_32173
  · decide +kernel

theorem prime_136397 : Nat.Prime 136397 := by
  apply nodeValid_prime [2, 13, 43, 61] ⟨136397, 2, [(2, 2), (13, 1), (43, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_61
  · decide +kernel

theorem prime_137831 : Nat.Prime 137831 := by
  apply nodeValid_prime [2, 5, 7, 11, 179] ⟨137831, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_179
  · decide +kernel

theorem prime_158843 : Nat.Prime 158843 := by
  apply nodeValid_prime [2, 43, 1847] ⟨158843, 2, [(2, 1), (43, 1), (1847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1847
  · decide +kernel

theorem prime_165397 : Nat.Prime 165397 := by
  apply nodeValid_prime [2, 3, 7, 11, 179] ⟨165397, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_179
  · decide +kernel

theorem prime_166973 : Nat.Prime 166973 := by
  apply nodeValid_prime [2, 13, 19] ⟨166973, 2, [(2, 2), (13, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_174481 : Nat.Prime 174481 := by
  apply nodeValid_prime [2, 3, 5, 727] ⟨174481, 7, [(2, 4), (3, 1), (5, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_727
  · decide +kernel

theorem prime_193009 : Nat.Prime 193009 := by
  apply nodeValid_prime [2, 3, 4021] ⟨193009, 7, [(2, 4), (3, 1), (4021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4021
  · decide +kernel

theorem prime_198967 : Nat.Prime 198967 := by
  apply nodeValid_prime [2, 3, 33161] ⟨198967, 5, [(2, 1), (3, 1), (33161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33161
  · decide +kernel

theorem prime_231241 : Nat.Prime 231241 := by
  apply nodeValid_prime [2, 3, 5, 41, 47] ⟨231241, 7, [(2, 3), (3, 1), (5, 1), (41, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_47
  · decide +kernel

theorem prime_261971 : Nat.Prime 261971 := by
  apply nodeValid_prime [2, 5, 17, 23, 67] ⟨261971, 6, [(2, 1), (5, 1), (17, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_265717 : Nat.Prime 265717 := by
  apply nodeValid_prime [2, 3, 11, 61] ⟨265717, 17, [(2, 2), (3, 2), (11, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_298691 : Nat.Prime 298691 := by
  apply nodeValid_prime [2, 5, 7, 17, 251] ⟨298691, 2, [(2, 1), (5, 1), (7, 1), (17, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_251
  · decide +kernel

theorem prime_349907 : Nat.Prime 349907 := by
  apply nodeValid_prime [2, 53, 3301] ⟨349907, 2, [(2, 1), (53, 1), (3301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_3301
  · decide +kernel

theorem prime_404387 : Nat.Prime 404387 := by
  apply nodeValid_prime [2, 23, 59, 149] ⟨404387, 2, [(2, 1), (23, 1), (59, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
    · exact prime_149
  · decide +kernel

theorem prime_580759 : Nat.Prime 580759 := by
  apply nodeValid_prime [2, 3, 43, 2251] ⟨580759, 3, [(2, 1), (3, 1), (43, 1), (2251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_2251
  · decide +kernel

theorem prime_597383 : Nat.Prime 597383 := by
  apply nodeValid_prime [2, 298691] ⟨597383, 5, [(2, 1), (298691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_298691
  · decide +kernel

theorem prime_606721 : Nat.Prime 606721 := by
  apply nodeValid_prime [2, 3, 5, 79] ⟨606721, 7, [(2, 9), (3, 1), (5, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_607573 : Nat.Prime 607573 := by
  apply nodeValid_prime [2, 3, 7, 2411] ⟨607573, 5, [(2, 2), (3, 2), (7, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2411
  · decide +kernel

theorem prime_614413 : Nat.Prime 614413 := by
  apply nodeValid_prime [2, 3, 5689] ⟨614413, 5, [(2, 2), (3, 3), (5689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5689
  · decide +kernel

theorem prime_625103 : Nat.Prime 625103 := by
  apply nodeValid_prime [2, 312551] ⟨625103, 5, [(2, 1), (312551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_312551
  · decide +kernel

theorem prime_646169 : Nat.Prime 646169 := by
  apply nodeValid_prime [2, 37, 59] ⟨646169, 3, [(2, 3), (37, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_918361 : Nat.Prime 918361 := by
  apply nodeValid_prime [2, 3, 5, 2551] ⟨918361, 7, [(2, 3), (3, 2), (5, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2551
  · decide +kernel

theorem prime_964757 : Nat.Prime 964757 := by
  apply nodeValid_prime [2, 13, 18553] ⟨964757, 2, [(2, 2), (13, 1), (18553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_18553
  · decide +kernel

theorem prime_1154849 : Nat.Prime 1154849 := by
  apply nodeValid_prime [2, 151, 239] ⟨1154849, 3, [(2, 5), (151, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_239
  · decide +kernel

theorem prime_1184741 : Nat.Prime 1184741 := by
  apply nodeValid_prime [2, 5, 37, 1601] ⟨1184741, 3, [(2, 2), (5, 1), (37, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1601
  · decide +kernel

theorem prime_1467443 : Nat.Prime 1467443 := by
  apply nodeValid_prime [2, 179, 4099] ⟨1467443, 2, [(2, 1), (179, 1), (4099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_4099
  · decide +kernel

theorem prime_1514063 : Nat.Prime 1514063 := by
  apply nodeValid_prime [2, 11, 68821] ⟨1514063, 10, [(2, 1), (11, 1), (68821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_68821
  · decide +kernel

theorem prime_1588049 : Nat.Prime 1588049 := by
  apply nodeValid_prime [2, 7, 11, 1289] ⟨1588049, 3, [(2, 4), (7, 1), (11, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1289
  · decide +kernel

theorem prime_1603417 : Nat.Prime 1603417 := by
  apply nodeValid_prime [2, 3, 66809] ⟨1603417, 5, [(2, 3), (3, 1), (66809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66809
  · decide +kernel

theorem prime_1806527 : Nat.Prime 1806527 := by
  apply nodeValid_prime [2, 29, 31147] ⟨1806527, 5, [(2, 1), (29, 1), (31147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_31147
  · decide +kernel

theorem prime_2009713 : Nat.Prime 2009713 := by
  apply nodeValid_prime [2, 3, 149, 281] ⟨2009713, 5, [(2, 4), (3, 1), (149, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_281
  · decide +kernel

theorem prime_2323037 : Nat.Prime 2323037 := by
  apply nodeValid_prime [2, 580759] ⟨2323037, 2, [(2, 2), (580759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_580759
  · decide +kernel

theorem prime_3120791 : Nat.Prime 3120791 := by
  apply nodeValid_prime [2, 5, 521, 599] ⟨3120791, 7, [(2, 1), (5, 1), (521, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_521
    · exact prime_599
  · decide +kernel

theorem prime_3855029 : Nat.Prime 3855029 := by
  apply nodeValid_prime [2, 29, 167, 199] ⟨3855029, 2, [(2, 2), (29, 1), (167, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_167
    · exact prime_199
  · decide +kernel

theorem prime_4391851 : Nat.Prime 4391851 := by
  apply nodeValid_prime [2, 3, 5, 19, 23, 67] ⟨4391851, 2, [(2, 1), (3, 1), (5, 2), (19, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_6132167 : Nat.Prime 6132167 := by
  apply nodeValid_prime [2, 29, 105727] ⟨6132167, 5, [(2, 1), (29, 1), (105727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_105727
  · decide +kernel

theorem prime_6194189 : Nat.Prime 6194189 := by
  apply nodeValid_prime [2, 7, 11, 13, 17] ⟨6194189, 3, [(2, 2), (7, 2), (11, 1), (13, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_6819851 : Nat.Prime 6819851 := by
  apply nodeValid_prime [2, 5, 136397] ⟨6819851, 11, [(2, 1), (5, 2), (136397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_136397
  · decide +kernel

theorem prime_7187767 : Nat.Prime 7187767 := by
  apply nodeValid_prime [2, 3, 29, 101, 409] ⟨7187767, 10, [(2, 1), (3, 1), (29, 1), (101, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_101
    · exact prime_409
  · decide +kernel

theorem prime_7751489 : Nat.Prime 7751489 := by
  apply nodeValid_prime [2, 31, 3907] ⟨7751489, 3, [(2, 6), (31, 1), (3907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3907
  · decide +kernel

theorem prime_8609501 : Nat.Prime 8609501 := by
  apply nodeValid_prime [2, 5, 67, 257] ⟨8609501, 2, [(2, 2), (5, 3), (67, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_257
  · decide +kernel

theorem prime_13347863 : Nat.Prime 13347863 := by
  apply nodeValid_prime [2, 11, 606721] ⟨13347863, 5, [(2, 1), (11, 1), (606721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_606721
  · decide +kernel

theorem prime_13538597 : Nat.Prime 13538597 := by
  apply nodeValid_prime [2, 17, 37, 5381] ⟨13538597, 2, [(2, 2), (17, 1), (37, 1), (5381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_5381
  · decide +kernel

theorem prime_16026001 : Nat.Prime 16026001 := by
  apply nodeValid_prime [2, 3, 5, 2671] ⟨16026001, 7, [(2, 4), (3, 1), (5, 3), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2671
  · decide +kernel

theorem prime_24682193 : Nat.Prime 24682193 := by
  apply nodeValid_prime [2, 89, 17333] ⟨24682193, 3, [(2, 4), (89, 1), (17333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_17333
  · decide +kernel

theorem prime_34777283 : Nat.Prime 34777283 := by
  apply nodeValid_prime [2, 43, 404387] ⟨34777283, 2, [(2, 1), (43, 1), (404387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_404387
  · decide +kernel

theorem prime_47870089 : Nat.Prime 47870089 := by
  apply nodeValid_prime [2, 3, 7, 107, 2663] ⟨47870089, 13, [(2, 3), (3, 1), (7, 1), (107, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_2663
  · decide +kernel

theorem prime_53218927 : Nat.Prime 53218927 := by
  apply nodeValid_prime [2, 3, 149, 19843] ⟨53218927, 3, [(2, 1), (3, 2), (149, 1), (19843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_19843
  · decide +kernel

theorem prime_54517531 : Nat.Prime 54517531 := by
  apply nodeValid_prime [2, 3, 5, 31, 61] ⟨54517531, 2, [(2, 1), (3, 1), (5, 1), (31, 3), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_61
  · decide +kernel

theorem prime_58178581 : Nat.Prime 58178581 := by
  apply nodeValid_prime [2, 3, 5, 179, 5417] ⟨58178581, 2, [(2, 2), (3, 1), (5, 1), (179, 1), (5417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_5417
  · decide +kernel

theorem prime_81739261 : Nat.Prime 81739261 := by
  apply nodeValid_prime [2, 3, 5, 229, 661] ⟨81739261, 13, [(2, 2), (3, 3), (5, 1), (229, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_229
    · exact prime_661
  · decide +kernel

theorem prime_92387921 : Nat.Prime 92387921 := by
  apply nodeValid_prime [2, 5, 1154849] ⟨92387921, 3, [(2, 4), (5, 1), (1154849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1154849
  · decide +kernel

theorem prime_95232821 : Nat.Prime 95232821 := by
  apply nodeValid_prime [2, 5, 37, 128693] ⟨95232821, 2, [(2, 2), (5, 1), (37, 1), (128693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_128693
  · decide +kernel

theorem prime_181901471 : Nat.Prime 181901471 := by
  apply nodeValid_prime [2, 5, 421, 43207] ⟨181901471, 13, [(2, 1), (5, 1), (421, 1), (43207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_421
    · exact prime_43207
  · decide +kernel

theorem prime_218235233 : Nat.Prime 218235233 := by
  apply nodeValid_prime [2, 6819851] ⟨218235233, 3, [(2, 5), (6819851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6819851
  · decide +kernel

theorem prime_243559441 : Nat.Prime 243559441 := by
  apply nodeValid_prime [2, 3, 5, 112759] ⟨243559441, 7, [(2, 4), (3, 3), (5, 1), (112759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_112759
  · decide +kernel

theorem prime_360573611 : Nat.Prime 360573611 := by
  apply nodeValid_prime [2, 5, 227, 158843] ⟨360573611, 2, [(2, 1), (5, 1), (227, 1), (158843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
    · exact prime_158843
  · decide +kernel

theorem prime_402243407 : Nat.Prime 402243407 := by
  apply nodeValid_prime [2, 2207, 91129] ⟨402243407, 5, [(2, 1), (2207, 1), (91129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2207
    · exact prime_91129
  · decide +kernel

theorem prime_402550403 : Nat.Prime 402550403 := by
  apply nodeValid_prime [2, 13619, 14779] ⟨402550403, 2, [(2, 1), (13619, 1), (14779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13619
    · exact prime_14779
  · decide +kernel

theorem prime_428352109 : Nat.Prime 428352109 := by
  apply nodeValid_prime [2, 3, 37, 964757] ⟨428352109, 6, [(2, 2), (3, 1), (37, 1), (964757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_964757
  · decide +kernel

theorem prime_930857297 : Nat.Prime 930857297 := by
  apply nodeValid_prime [2, 58178581] ⟨930857297, 3, [(2, 4), (58178581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58178581
  · decide +kernel

theorem prime_1495331581 : Nat.Prime 1495331581 := by
  apply nodeValid_prime [2, 3, 5, 383, 65071] ⟨1495331581, 2, [(2, 2), (3, 1), (5, 1), (383, 1), (65071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_383
    · exact prime_65071
  · decide +kernel

theorem prime_1763866487 : Nat.Prime 1763866487 := by
  apply nodeValid_prime [2, 601, 1467443] ⟨1763866487, 5, [(2, 1), (601, 1), (1467443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_601
    · exact prime_1467443
  · decide +kernel

theorem prime_8543329313 : Nat.Prime 8543329313 := by
  apply nodeValid_prime [2, 7, 109, 349907] ⟨8543329313, 3, [(2, 5), (7, 1), (109, 1), (349907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109
    · exact prime_349907
  · decide +kernel

theorem prime_8585033801 : Nat.Prime 8585033801 := by
  apply nodeValid_prime [2, 5, 7, 6132167] ⟨8585033801, 3, [(2, 3), (5, 2), (7, 1), (6132167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6132167
  · decide +kernel

theorem prime_8602782907 : Nat.Prime 8602782907 := by
  apply nodeValid_prime [2, 3, 31, 277, 166973] ⟨8602782907, 2, [(2, 1), (3, 1), (31, 1), (277, 1), (166973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_277
    · exact prime_166973
  · decide +kernel

theorem prime_16760976497 : Nat.Prime 16760976497 := by
  apply nodeValid_prime [2, 11, 95232821] ⟨16760976497, 3, [(2, 4), (11, 1), (95232821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_95232821
  · decide +kernel

theorem prime_17086658627 : Nat.Prime 17086658627 := by
  apply nodeValid_prime [2, 8543329313] ⟨17086658627, 2, [(2, 1), (8543329313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8543329313
  · decide +kernel

theorem prime_19447200823 : Nat.Prime 19447200823 := by
  apply nodeValid_prime [2, 3, 7, 2399, 193009] ⟨19447200823, 5, [(2, 1), (3, 1), (7, 1), (2399, 1), (193009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2399
    · exact prime_193009
  · decide +kernel

theorem prime_21536812771 : Nat.Prime 21536812771 := by
  apply nodeValid_prime [2, 3, 5, 11, 101, 646169] ⟨21536812771, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (101, 1), (646169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_101
    · exact prime_646169
  · decide +kernel

theorem prime_26260103399 : Nat.Prime 26260103399 := by
  apply nodeValid_prime [2, 23, 10627, 53719] ⟨26260103399, 19, [(2, 1), (23, 1), (10627, 1), (53719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_10627
    · exact prime_53719
  · decide +kernel

theorem prime_28895348857 : Nat.Prime 28895348857 := by
  apply nodeValid_prime [2, 3, 11, 157, 63377] ⟨28895348857, 5, [(2, 3), (3, 1), (11, 2), (157, 1), (63377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_157
    · exact prime_63377
  · decide +kernel

theorem prime_34060113281 : Nat.Prime 34060113281 := by
  apply nodeValid_prime [2, 5, 53218927] ⟨34060113281, 3, [(2, 7), (5, 1), (53218927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53218927
  · decide +kernel

theorem prime_98794117537 : Nat.Prime 98794117537 := by
  apply nodeValid_prime [2, 3, 443, 2323037] ⟨98794117537, 5, [(2, 5), (3, 1), (443, 1), (2323037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_443
    · exact prime_2323037
  · decide +kernel

theorem prime_148910100007 : Nat.Prime 148910100007 := by
  apply nodeValid_prime [2, 3, 5651, 4391851] ⟨148910100007, 3, [(2, 1), (3, 1), (5651, 1), (4391851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5651
    · exact prime_4391851
  · decide +kernel

theorem prime_153673356253 : Nat.Prime 153673356253 := by
  apply nodeValid_prime [2, 3, 13, 4951, 198967] ⟨153673356253, 2, [(2, 2), (3, 1), (13, 1), (4951, 1), (198967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4951
    · exact prime_198967
  · decide +kernel

theorem prime_237927124069 : Nat.Prime 237927124069 := by
  apply nodeValid_prime [2, 3, 109, 181901471] ⟨237927124069, 6, [(2, 2), (3, 1), (109, 1), (181901471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_181901471
  · decide +kernel

theorem prime_274721081633 : Nat.Prime 274721081633 := by
  apply nodeValid_prime [2, 8585033801] ⟨274721081633, 3, [(2, 5), (8585033801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8585033801
  · decide +kernel

theorem prime_352958862689 : Nat.Prime 352958862689 := by
  apply nodeValid_prime [2, 47699, 231241] ⟨352958862689, 3, [(2, 5), (47699, 1), (231241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47699
    · exact prime_231241
  · decide +kernel

theorem prime_395176470149 : Nat.Prime 395176470149 := by
  apply nodeValid_prime [2, 98794117537] ⟨395176470149, 2, [(2, 2), (98794117537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_98794117537
  · decide +kernel

theorem prime_1762347257659 : Nat.Prime 1762347257659 := by
  apply nodeValid_prime [2, 3, 13, 163, 1184741] ⟨1762347257659, 3, [(2, 1), (3, 3), (13, 2), (163, 1), (1184741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_163
    · exact prime_1184741
  · decide +kernel

theorem prime_1770921958807 : Nat.Prime 1770921958807 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 877, 37357] ⟨1770921958807, 3, [(2, 1), (3, 3), (7, 1), (11, 1), (13, 1), (877, 1), (37357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_877
    · exact prime_37357
  · decide +kernel

theorem prime_7034724130117 : Nat.Prime 7034724130117 := by
  apply nodeValid_prime [2, 3, 10753, 54517531] ⟨7034724130117, 2, [(2, 2), (3, 1), (10753, 1), (54517531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10753
    · exact prime_54517531
  · decide +kernel

theorem prime_7034724192767 : Nat.Prime 7034724192767 := by
  apply nodeValid_prime [2, 3863, 10399, 87559] ⟨7034724192767, 5, [(2, 1), (3863, 1), (10399, 1), (87559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3863
    · exact prime_10399
    · exact prime_87559
  · decide +kernel

theorem prime_7039610127703 : Nat.Prime 7039610127703 := by
  apply nodeValid_prime [2, 3, 9629, 13538597] ⟨7039610127703, 3, [(2, 1), (3, 3), (9629, 1), (13538597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9629
    · exact prime_13538597
  · decide +kernel

theorem prime_7039610128741 : Nat.Prime 7039610128741 := by
  apply nodeValid_prime [2, 3, 5, 7, 16760976497] ⟨7039610128741, 10, [(2, 2), (3, 1), (5, 1), (7, 1), (16760976497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_16760976497
  · decide +kernel

theorem prime_7039610149657 : Nat.Prime 7039610149657 := by
  apply nodeValid_prime [2, 3, 7, 31, 157, 8609501] ⟨7039610149657, 5, [(2, 3), (3, 1), (7, 1), (31, 1), (157, 1), (8609501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_157
    · exact prime_8609501
  · decide +kernel

theorem prime_7044498467659 : Nat.Prime 7044498467659 := by
  apply nodeValid_prime [2, 3, 67, 1217, 23879] ⟨7044498467659, 3, [(2, 1), (3, 3), (67, 2), (1217, 1), (23879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_1217
    · exact prime_23879
  · decide +kernel

theorem prime_7044498578681 : Nat.Prime 7044498578681 := by
  apply nodeValid_prime [2, 5, 101, 14411, 120997] ⟨7044498578681, 3, [(2, 3), (5, 1), (101, 1), (14411, 1), (120997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_14411
    · exact prime_120997
  · decide +kernel

theorem prime_7044498579743 : Nat.Prime 7044498579743 := by
  apply nodeValid_prime [2, 13, 79, 149, 167, 137831] ⟨7044498579743, 5, [(2, 1), (13, 1), (79, 1), (149, 1), (167, 1), (137831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_149
    · exact prime_167
    · exact prime_137831
  · decide +kernel

theorem prime_7049389030637 : Nat.Prime 7049389030637 := by
  apply nodeValid_prime [2, 1762347257659] ⟨7049389030637, 2, [(2, 2), (1762347257659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1762347257659
  · decide +kernel

theorem prime_7049389030951 : Nat.Prime 7049389030951 := by
  apply nodeValid_prime [2, 3, 5, 7, 71, 3359, 28151] ⟨7049389030951, 6, [(2, 1), (3, 1), (5, 2), (7, 1), (71, 1), (3359, 1), (28151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_71
    · exact prime_3359
    · exact prime_28151
  · decide +kernel

theorem prime_7049389080247 : Nat.Prime 7049389080247 := by
  apply nodeValid_prime [2, 3, 23, 73, 103, 193, 35201] ⟨7049389080247, 3, [(2, 1), (3, 1), (23, 1), (73, 1), (103, 1), (193, 1), (35201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_73
    · exact prime_103
    · exact prime_193
    · exact prime_35201
  · decide +kernel

theorem prime_7054281983741 : Nat.Prime 7054281983741 := by
  apply nodeValid_prime [2, 5, 41, 8602782907] ⟨7054281983741, 2, [(2, 2), (5, 1), (41, 1), (8602782907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_8602782907
  · decide +kernel

theorem prime_7054281983887 : Nat.Prime 7054281983887 := by
  apply nodeValid_prime [2, 3, 17, 115771, 597383] ⟨7054281983887, 3, [(2, 1), (3, 1), (17, 1), (115771, 1), (597383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_115771
    · exact prime_597383
  · decide +kernel

theorem prime_7054281990923 : Nat.Prime 7054281990923 := by
  apply nodeValid_prime [2, 353, 5531, 1806527] ⟨7054281990923, 2, [(2, 1), (353, 1), (5531, 1), (1806527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_5531
    · exact prime_1806527
  · decide +kernel

theorem prime_7059177203891 : Nat.Prime 7059177203891 := by
  apply nodeValid_prime [2, 5, 7, 19, 139, 2009713] ⟨7059177203891, 2, [(2, 1), (5, 1), (7, 1), (19, 2), (139, 1), (2009713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_139
    · exact prime_2009713
  · decide +kernel

theorem prime_7059177253781 : Nat.Prime 7059177253781 := by
  apply nodeValid_prime [2, 5, 352958862689] ⟨7059177253781, 2, [(2, 2), (5, 1), (352958862689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_352958862689
  · decide +kernel

theorem prime_7059177256379 : Nat.Prime 7059177256379 := by
  apply nodeValid_prime [2, 13, 47, 59, 1567, 62483] ⟨7059177256379, 2, [(2, 1), (13, 1), (47, 1), (59, 1), (1567, 1), (62483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_59
    · exact prime_1567
    · exact prime_62483
  · decide +kernel

theorem prime_7064074588213 : Nat.Prime 7064074588213 := by
  apply nodeValid_prime [2, 3, 73, 1259, 9749] ⟨7064074588213, 2, [(2, 2), (3, 3), (73, 2), (1259, 1), (9749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_1259
    · exact prime_9749
  · decide +kernel

theorem prime_7064074588889 : Nat.Prime 7064074588889 := by
  apply nodeValid_prime [2, 41, 21536812771] ⟨7064074588889, 3, [(2, 3), (41, 1), (21536812771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_21536812771
  · decide +kernel

theorem prime_7064074721777 : Nat.Prime 7064074721777 := by
  apply nodeValid_prime [2, 863, 4373, 116989] ⟨7064074721777, 3, [(2, 4), (863, 1), (4373, 1), (116989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_863
    · exact prime_4373
    · exact prime_116989
  · decide +kernel

theorem prime_7068974387359 : Nat.Prime 7068974387359 := by
  apply nodeValid_prime [2, 3, 13, 23509, 3855029] ⟨7068974387359, 3, [(2, 1), (3, 1), (13, 1), (23509, 1), (3855029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23509
    · exact prime_3855029
  · decide +kernel

theorem prime_7068974387639 : Nat.Prime 7068974387639 := by
  apply nodeValid_prime [2, 23, 153673356253] ⟨7068974387639, 13, [(2, 1), (23, 1), (153673356253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_153673356253
  · decide +kernel

theorem prime_7068974543503 : Nat.Prime 7068974543503 := by
  apply nodeValid_prime [2, 3, 61, 83, 383, 607573] ⟨7068974543503, 5, [(2, 1), (3, 1), (61, 1), (83, 1), (383, 1), (607573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_83
    · exact prime_383
    · exact prime_607573
  · decide +kernel

theorem prime_7073876671579 : Nat.Prime 7073876671579 := by
  apply nodeValid_prime [2, 3, 23, 17086658627] ⟨7073876671579, 2, [(2, 1), (3, 2), (23, 1), (17086658627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_17086658627
  · decide +kernel

theorem prime_7073876841401 : Nat.Prime 7073876841401 := by
  apply nodeValid_prime [2, 5, 2207, 16026001] ⟨7073876841401, 3, [(2, 3), (5, 2), (2207, 1), (16026001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2207
    · exact prime_16026001
  · decide +kernel

theorem prime_7073876842463 : Nat.Prime 7073876842463 := by
  apply nodeValid_prime [2, 19, 853, 218235233] ⟨7073876842463, 5, [(2, 1), (19, 1), (853, 1), (218235233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_853
    · exact prime_218235233
  · decide +kernel

theorem prime_7078781099573 : Nat.Prime 7078781099573 := by
  apply nodeValid_prime [2, 7, 13, 19447200823] ⟨7078781099573, 2, [(2, 2), (7, 1), (13, 1), (19447200823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_19447200823
  · decide +kernel

theorem prime_7078781131091 : Nat.Prime 7078781131091 := by
  apply nodeValid_prime [2, 5, 114281, 6194189] ⟨7078781131091, 2, [(2, 1), (5, 1), (114281, 1), (6194189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_114281
    · exact prime_6194189
  · decide +kernel

theorem prime_7078781131153 : Nat.Prime 7078781131153 := by
  apply nodeValid_prime [2, 3, 409, 360573611] ⟨7078781131153, 5, [(2, 4), (3, 1), (409, 1), (360573611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_409
    · exact prime_360573611
  · decide +kernel

theorem prime_7083687811793 : Nat.Prime 7083687811793 := by
  apply nodeValid_prime [2, 251, 1763866487] ⟨7083687811793, 3, [(2, 4), (251, 1), (1763866487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_1763866487
  · decide +kernel

theorem prime_7083687835229 : Nat.Prime 7083687835229 := by
  apply nodeValid_prime [2, 1770921958807] ⟨7083687835229, 2, [(2, 2), (1770921958807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1770921958807
  · decide +kernel

theorem prime_7083687836783 : Nat.Prime 7083687836783 := by
  apply nodeValid_prime [2, 43331, 81739261] ⟨7083687836783, 5, [(2, 1), (43331, 1), (81739261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43331
    · exact prime_81739261
  · decide +kernel

theorem prime_7088596800391 : Nat.Prime 7088596800391 := by
  apply nodeValid_prime [2, 3, 5, 7, 617, 3389, 5381] ⟨7088596800391, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (617, 1), (3389, 1), (5381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_617
    · exact prime_3389
    · exact prime_5381
  · decide +kernel

theorem prime_7088596800611 : Nat.Prime 7088596800611 := by
  apply nodeValid_prime [2, 5, 13, 107, 8999, 56629] ⟨7088596800611, 2, [(2, 1), (5, 1), (13, 1), (107, 1), (8999, 1), (56629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_107
    · exact prime_8999
    · exact prime_56629
  · decide +kernel

theorem prime_7088596821547 : Nat.Prime 7088596821547 := by
  apply nodeValid_prime [2, 3, 101, 1153, 100447] ⟨7088596821547, 2, [(2, 1), (3, 1), (101, 2), (1153, 1), (100447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1153
    · exact prime_100447
  · decide +kernel

theorem prime_7093508134373 : Nat.Prime 7093508134373 := by
  apply nodeValid_prime [2, 11, 19, 397, 2351, 9091] ⟨7093508134373, 2, [(2, 2), (11, 1), (19, 1), (397, 1), (2351, 1), (9091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_397
    · exact prime_2351
    · exact prime_9091
  · decide +kernel

theorem prime_7093508225543 : Nat.Prime 7093508225543 := by
  apply nodeValid_prime [2, 265717, 13347863] ⟨7093508225543, 5, [(2, 1), (265717, 1), (13347863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_265717
    · exact prime_13347863
  · decide +kernel

theorem prime_7093508225777 : Nat.Prime 7093508225777 := by
  apply nodeValid_prime [2, 7, 419, 577, 261971] ⟨7093508225777, 3, [(2, 4), (7, 1), (419, 1), (577, 1), (261971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_419
    · exact prime_577
    · exact prime_261971
  · decide +kernel

theorem prime_7098421758007 : Nat.Prime 7098421758007 := by
  apply nodeValid_prime [2, 3, 269, 4789, 918361] ⟨7098421758007, 21, [(2, 1), (3, 1), (269, 1), (4789, 1), (918361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_4789
    · exact prime_918361
  · decide +kernel

theorem prime_7098421758313 : Nat.Prime 7098421758313 := by
  apply nodeValid_prime [2, 3, 3821, 5387, 14369] ⟨7098421758313, 13, [(2, 3), (3, 1), (3821, 1), (5387, 1), (14369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3821
    · exact prime_5387
    · exact prime_14369
  · decide +kernel

theorem prime_7098421758419 : Nat.Prime 7098421758419 := by
  apply nodeValid_prime [2, 37, 757, 7457, 16993] ⟨7098421758419, 2, [(2, 1), (37, 1), (757, 1), (7457, 1), (16993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_757
    · exact prime_7457
    · exact prime_16993
  · decide +kernel

theorem prime_7103337687857 : Nat.Prime 7103337687857 := by
  apply nodeValid_prime [2, 17987, 24682193] ⟨7103337687857, 3, [(2, 4), (17987, 1), (24682193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17987
    · exact prime_24682193
  · decide +kernel

theorem prime_7103337694007 : Nat.Prime 7103337694007 := by
  apply nodeValid_prime [2, 37, 1039, 92387921] ⟨7103337694007, 5, [(2, 1), (37, 1), (1039, 1), (92387921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1039
    · exact prime_92387921
  · decide +kernel

theorem prime_7108255818823 : Nat.Prime 7108255818823 := by
  apply nodeValid_prime [2, 3, 41, 28895348857] ⟨7108255818823, 3, [(2, 1), (3, 1), (41, 1), (28895348857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_28895348857
  · decide +kernel

theorem prime_7108255820167 : Nat.Prime 7108255820167 := by
  apply nodeValid_prime [2, 3, 277, 6961, 614413] ⟨7108255820167, 3, [(2, 1), (3, 1), (277, 1), (6961, 1), (614413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_6961
    · exact prime_614413
  · decide +kernel

theorem prime_7108255921447 : Nat.Prime 7108255921447 := by
  apply nodeValid_prime [2, 3, 54941, 7187767] ⟨7108255921447, 5, [(2, 1), (3, 2), (54941, 1), (7187767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_54941
    · exact prime_7187767
  · decide +kernel

theorem prime_7113176462683 : Nat.Prime 7113176462683 := by
  apply nodeValid_prime [2, 3, 395176470149] ⟨7113176462683, 3, [(2, 1), (3, 2), (395176470149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_395176470149
  · decide +kernel

theorem prime_7113176513549 : Nat.Prime 7113176513549 := by
  apply nodeValid_prime [2, 7, 757, 2029, 165397] ⟨7113176513549, 2, [(2, 2), (7, 1), (757, 1), (2029, 1), (165397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_757
    · exact prime_2029
    · exact prime_165397
  · decide +kernel

theorem prime_7113176514163 : Nat.Prime 7113176514163 := by
  apply nodeValid_prime [2, 3, 23, 251, 691, 1223] ⟨7113176514163, 2, [(2, 1), (3, 6), (23, 1), (251, 1), (691, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_251
    · exact prime_691
    · exact prime_1223
  · decide +kernel

theorem prime_7118099308003 : Nat.Prime 7118099308003 := by
  apply nodeValid_prime [2, 3, 2017, 3371, 174481] ⟨7118099308003, 2, [(2, 1), (3, 1), (2017, 1), (3371, 1), (174481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2017
    · exact prime_3371
    · exact prime_174481
  · decide +kernel

theorem prime_7118099330273 : Nat.Prime 7118099330273 := by
  apply nodeValid_prime [2, 7, 79, 402243407] ⟨7118099330273, 3, [(2, 5), (7, 1), (79, 1), (402243407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_402243407
  · decide +kernel

theorem prime_7118099330833 : Nat.Prime 7118099330833 := by
  apply nodeValid_prime [2, 3, 7, 911, 7751489] ⟨7118099330833, 5, [(2, 4), (3, 2), (7, 1), (911, 1), (7751489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_911
    · exact prime_7751489
  · decide +kernel

theorem prime_7123024451623 : Nat.Prime 7123024451623 := by
  apply nodeValid_prime [2, 3, 197, 1931, 3120791] ⟨7123024451623, 3, [(2, 1), (3, 1), (197, 1), (1931, 1), (3120791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1931
    · exact prime_3120791
  · decide +kernel

theorem prime_7123024452289 : Nat.Prime 7123024452289 := by
  apply nodeValid_prime [2, 3, 107, 229, 1514063] ⟨7123024452289, 13, [(2, 6), (3, 1), (107, 1), (229, 1), (1514063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_229
    · exact prime_1514063
  · decide +kernel

theorem prime_7123024464701 : Nat.Prime 7123024464701 := by
  apply nodeValid_prime [2, 5, 17, 101, 107, 109, 3557] ⟨7123024464701, 2, [(2, 2), (5, 2), (17, 1), (101, 1), (107, 1), (109, 1), (3557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_101
    · exact prime_107
    · exact prime_109
    · exact prime_3557
  · decide +kernel

theorem prime_7127951923681 : Nat.Prime 7127951923681 := by
  apply nodeValid_prime [2, 3, 5, 7, 61, 34777283] ⟨7127951923681, 22, [(2, 5), (3, 1), (5, 1), (7, 1), (61, 1), (34777283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_34777283
  · decide +kernel

theorem prime_7127951992279 : Nat.Prime 7127951992279 := by
  apply nodeValid_prime [2, 3, 13, 23, 83, 47870089] ⟨7127951992279, 6, [(2, 1), (3, 1), (13, 1), (23, 1), (83, 1), (47870089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_83
    · exact prime_47870089
  · decide +kernel

theorem prime_7127951992933 : Nat.Prime 7127951992933 := by
  apply nodeValid_prime [2, 3, 53, 17929, 625103] ⟨7127951992933, 5, [(2, 2), (3, 1), (53, 1), (17929, 1), (625103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_17929
    · exact prime_625103
  · decide +kernel

theorem prime_7132881684259 : Nat.Prime 7132881684259 := by
  apply nodeValid_prime [2, 3, 11, 307, 8467, 13859] ⟨7132881684259, 3, [(2, 1), (3, 2), (11, 1), (307, 1), (8467, 1), (13859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_307
    · exact prime_8467
    · exact prime_13859
  · decide +kernel

theorem prime_7132881789091 : Nat.Prime 7132881789091 := by
  apply nodeValid_prime [2, 3, 5, 59, 71, 3709, 5101] ⟨7132881789091, 7, [(2, 1), (3, 2), (5, 1), (59, 1), (71, 1), (3709, 1), (5101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_71
    · exact prime_3709
    · exact prime_5101
  · decide +kernel

theorem prime_7132881789127 : Nat.Prime 7132881789127 := by
  apply nodeValid_prime [2, 3, 1627, 243559441] ⟨7132881789127, 3, [(2, 1), (3, 2), (1627, 1), (243559441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1627
    · exact prime_243559441
  · decide +kernel

theorem prime_7137813722071 : Nat.Prime 7137813722071 := by
  apply nodeValid_prime [2, 3, 5, 237927124069] ⟨7137813722071, 3, [(2, 1), (3, 1), (5, 1), (237927124069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_237927124069
  · decide +kernel

theorem prime_7137813723091 : Nat.Prime 7137813723091 := by
  apply nodeValid_prime [2, 3, 5, 197, 761, 1063, 1493] ⟨7137813723091, 2, [(2, 1), (3, 1), (5, 1), (197, 1), (761, 1), (1063, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
    · exact prime_761
    · exact prime_1063
    · exact prime_1493
  · decide +kernel

theorem prime_7137813753397 : Nat.Prime 7137813753397 := by
  apply nodeValid_prime [2, 3, 71, 930857297] ⟨7137813753397, 6, [(2, 2), (3, 3), (71, 1), (930857297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_930857297
  · decide +kernel

theorem prime_7142748122459 : Nat.Prime 7142748122459 := by
  apply nodeValid_prime [2, 13, 274721081633] ⟨7142748122459, 2, [(2, 1), (13, 1), (274721081633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_274721081633
  · decide +kernel

theorem prime_7142748123569 : Nat.Prime 7142748123569 := by
  apply nodeValid_prime [2, 433, 643, 1603417] ⟨7142748123569, 3, [(2, 4), (433, 1), (643, 1), (1603417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_433
    · exact prime_643
    · exact prime_1603417
  · decide +kernel

theorem prime_7142748124529 : Nat.Prime 7142748124529 := by
  apply nodeValid_prime [2, 17, 26260103399] ⟨7142748124529, 6, [(2, 4), (17, 1), (26260103399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_26260103399
  · decide +kernel

theorem prime_7147684800337 : Nat.Prime 7147684800337 := by
  apply nodeValid_prime [2, 3, 148910100007] ⟨7147684800337, 5, [(2, 4), (3, 1), (148910100007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_148910100007
  · decide +kernel

theorem prime_7147684955669 : Nat.Prime 7147684955669 := by
  apply nodeValid_prime [2, 23, 193, 402550403] ⟨7147684955669, 2, [(2, 2), (23, 1), (193, 1), (402550403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_193
    · exact prime_402550403
  · decide +kernel

theorem prime_7147684957181 : Nat.Prime 7147684957181 := by
  apply nodeValid_prime [2, 5, 239, 1495331581] ⟨7147684957181, 2, [(2, 2), (5, 1), (239, 1), (1495331581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_1495331581
  · decide +kernel

theorem prime_7152623513569 : Nat.Prime 7152623513569 := by
  apply nodeValid_prime [2, 3, 13, 401, 1588049] ⟨7152623513569, 11, [(2, 5), (3, 3), (13, 1), (401, 1), (1588049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_401
    · exact prime_1588049
  · decide +kernel

theorem prime_7152623516083 : Nat.Prime 7152623516083 := by
  apply nodeValid_prime [2, 3, 11, 23, 428352109] ⟨7152623516083, 2, [(2, 1), (3, 1), (11, 2), (23, 1), (428352109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_428352109
  · decide +kernel

theorem prime_7152623789011 : Nat.Prime 7152623789011 := by
  apply nodeValid_prime [2, 3, 5, 7, 34060113281] ⟨7152623789011, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (34060113281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_34060113281
  · decide +kernel

end Sude.Lucas.Generated
