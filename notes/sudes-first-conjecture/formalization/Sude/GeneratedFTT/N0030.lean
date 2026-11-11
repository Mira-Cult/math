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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1973 : Nat.Prime 1973 := by
  apply nodeValid_prime [2, 17, 29] ⟨1973, 2, [(2, 2), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_3517 : Nat.Prime 3517 := by
  apply nodeValid_prime [2, 3, 293] ⟨3517, 2, [(2, 2), (3, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
  · decide +kernel

theorem prime_3919 : Nat.Prime 3919 := by
  apply nodeValid_prime [2, 3, 653] ⟨3919, 3, [(2, 1), (3, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
  · decide +kernel

theorem prime_4567 : Nat.Prime 4567 := by
  apply nodeValid_prime [2, 3, 761] ⟨4567, 3, [(2, 1), (3, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_761
  · decide +kernel

theorem prime_5791 : Nat.Prime 5791 := by
  apply nodeValid_prime [2, 3, 5, 193] ⟨5791, 6, [(2, 1), (3, 1), (5, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_193
  · decide +kernel

theorem prime_6029 : Nat.Prime 6029 := by
  apply nodeValid_prime [2, 11, 137] ⟨6029, 2, [(2, 2), (11, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_137
  · decide +kernel

theorem prime_6121 : Nat.Prime 6121 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨6121, 7, [(2, 3), (3, 2), (5, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_8731 : Nat.Prime 8731 := by
  apply nodeValid_prime [2, 3, 5, 97] ⟨8731, 2, [(2, 1), (3, 2), (5, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_10093 : Nat.Prime 10093 := by
  apply nodeValid_prime [2, 3, 29] ⟨10093, 2, [(2, 2), (3, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_10211 : Nat.Prime 10211 := by
  apply nodeValid_prime [2, 5, 1021] ⟨10211, 6, [(2, 1), (5, 1), (1021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1021
  · decide +kernel

theorem prime_12107 : Nat.Prime 12107 := by
  apply nodeValid_prime [2, 6053] ⟨12107, 2, [(2, 1), (6053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6053
  · decide +kernel

theorem prime_14549 : Nat.Prime 14549 := by
  apply nodeValid_prime [2, 3637] ⟨14549, 2, [(2, 2), (3637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3637
  · decide +kernel

theorem prime_14657 : Nat.Prime 14657 := by
  apply nodeValid_prime [2, 229] ⟨14657, 3, [(2, 6), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_229
  · decide +kernel

theorem prime_16249 : Nat.Prime 16249 := by
  apply nodeValid_prime [2, 3, 677] ⟨16249, 17, [(2, 3), (3, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
  · decide +kernel

theorem prime_17047 : Nat.Prime 17047 := by
  apply nodeValid_prime [2, 3, 947] ⟨17047, 3, [(2, 1), (3, 2), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_947
  · decide +kernel

theorem prime_17327 : Nat.Prime 17327 := by
  apply nodeValid_prime [2, 8663] ⟨17327, 5, [(2, 1), (8663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8663
  · decide +kernel

theorem prime_18311 : Nat.Prime 18311 := by
  apply nodeValid_prime [2, 5, 1831] ⟨18311, 13, [(2, 1), (5, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1831
  · decide +kernel

theorem prime_20707 : Nat.Prime 20707 := by
  apply nodeValid_prime [2, 3, 7, 17, 29] ⟨20707, 5, [(2, 1), (3, 1), (7, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_20897 : Nat.Prime 20897 := by
  apply nodeValid_prime [2, 653] ⟨20897, 3, [(2, 5), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_653
  · decide +kernel

theorem prime_21523 : Nat.Prime 21523 := by
  apply nodeValid_prime [2, 3, 17, 211] ⟨21523, 2, [(2, 1), (3, 1), (17, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_211
  · decide +kernel

theorem prime_21821 : Nat.Prime 21821 := by
  apply nodeValid_prime [2, 5, 1091] ⟨21821, 2, [(2, 2), (5, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1091
  · decide +kernel

theorem prime_23333 : Nat.Prime 23333 := by
  apply nodeValid_prime [2, 19, 307] ⟨23333, 2, [(2, 2), (19, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_307
  · decide +kernel

theorem prime_31079 : Nat.Prime 31079 := by
  apply nodeValid_prime [2, 41, 379] ⟨31079, 11, [(2, 1), (41, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_379
  · decide +kernel

theorem prime_33829 : Nat.Prime 33829 := by
  apply nodeValid_prime [2, 3, 2819] ⟨33829, 2, [(2, 2), (3, 1), (2819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2819
  · decide +kernel

theorem prime_34961 : Nat.Prime 34961 := by
  apply nodeValid_prime [2, 5, 19, 23] ⟨34961, 3, [(2, 4), (5, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_45121 : Nat.Prime 45121 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨45121, 7, [(2, 6), (3, 1), (5, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_46993 : Nat.Prime 46993 := by
  apply nodeValid_prime [2, 3, 11, 89] ⟨46993, 5, [(2, 4), (3, 1), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_48973 : Nat.Prime 48973 := by
  apply nodeValid_prime [2, 3, 7, 11, 53] ⟨48973, 5, [(2, 2), (3, 1), (7, 1), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_49871 : Nat.Prime 49871 := by
  apply nodeValid_prime [2, 5, 4987] ⟨49871, 17, [(2, 1), (5, 1), (4987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4987
  · decide +kernel

theorem prime_53639 : Nat.Prime 53639 := by
  apply nodeValid_prime [2, 13, 2063] ⟨53639, 11, [(2, 1), (13, 1), (2063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2063
  · decide +kernel

theorem prime_55343 : Nat.Prime 55343 := by
  apply nodeValid_prime [2, 7, 59, 67] ⟨55343, 7, [(2, 1), (7, 1), (59, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_67
  · decide +kernel

theorem prime_55501 : Nat.Prime 55501 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨55501, 6, [(2, 2), (3, 1), (5, 3), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_60637 : Nat.Prime 60637 := by
  apply nodeValid_prime [2, 3, 31, 163] ⟨60637, 2, [(2, 2), (3, 1), (31, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_163
  · decide +kernel

theorem prime_64951 : Nat.Prime 64951 := by
  apply nodeValid_prime [2, 3, 5, 433] ⟨64951, 3, [(2, 1), (3, 1), (5, 2), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_433
  · decide +kernel

theorem prime_67523 : Nat.Prime 67523 := by
  apply nodeValid_prime [2, 7, 13, 53] ⟨67523, 2, [(2, 1), (7, 2), (13, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_70501 : Nat.Prime 70501 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨70501, 2, [(2, 2), (3, 1), (5, 3), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_80929 : Nat.Prime 80929 := by
  apply nodeValid_prime [2, 3, 281] ⟨80929, 19, [(2, 5), (3, 2), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
  · decide +kernel

theorem prime_83561 : Nat.Prime 83561 := by
  apply nodeValid_prime [2, 5, 2089] ⟨83561, 3, [(2, 3), (5, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2089
  · decide +kernel

theorem prime_138617 : Nat.Prime 138617 := by
  apply nodeValid_prime [2, 17327] ⟨138617, 3, [(2, 3), (17327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17327
  · decide +kernel

theorem prime_146891 : Nat.Prime 146891 := by
  apply nodeValid_prime [2, 5, 37, 397] ⟨146891, 2, [(2, 1), (5, 1), (37, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_397
  · decide +kernel

theorem prime_157133 : Nat.Prime 157133 := by
  apply nodeValid_prime [2, 163, 241] ⟨157133, 2, [(2, 2), (163, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_241
  · decide +kernel

theorem prime_161599 : Nat.Prime 161599 := by
  apply nodeValid_prime [2, 3, 23, 1171] ⟨161599, 6, [(2, 1), (3, 1), (23, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1171
  · decide +kernel

theorem prime_166237 : Nat.Prime 166237 := by
  apply nodeValid_prime [2, 3, 7, 1979] ⟨166237, 2, [(2, 2), (3, 1), (7, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1979
  · decide +kernel

theorem prime_166783 : Nat.Prime 166783 := by
  apply nodeValid_prime [2, 3, 7, 11, 19] ⟨166783, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (19, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_174569 : Nat.Prime 174569 := by
  apply nodeValid_prime [2, 21821] ⟨174569, 3, [(2, 3), (21821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21821
  · decide +kernel

theorem prime_191251 : Nat.Prime 191251 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨191251, 10, [(2, 1), (3, 2), (5, 4), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_193337 : Nat.Prime 193337 := by
  apply nodeValid_prime [2, 11, 13] ⟨193337, 3, [(2, 3), (11, 1), (13, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_196453 : Nat.Prime 196453 := by
  apply nodeValid_prime [2, 3, 17, 107] ⟨196453, 6, [(2, 2), (3, 3), (17, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_107
  · decide +kernel

theorem prime_238103 : Nat.Prime 238103 := by
  apply nodeValid_prime [2, 17, 47, 149] ⟨238103, 5, [(2, 1), (17, 1), (47, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_149
  · decide +kernel

theorem prime_288991 : Nat.Prime 288991 := by
  apply nodeValid_prime [2, 3, 5, 13, 19] ⟨288991, 3, [(2, 1), (3, 2), (5, 1), (13, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_318271 : Nat.Prime 318271 := by
  apply nodeValid_prime [2, 3, 5, 103] ⟨318271, 3, [(2, 1), (3, 1), (5, 1), (103, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_397181 : Nat.Prime 397181 := by
  apply nodeValid_prime [2, 5, 7, 2837] ⟨397181, 2, [(2, 2), (5, 1), (7, 1), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2837
  · decide +kernel

theorem prime_422041 : Nat.Prime 422041 := by
  apply nodeValid_prime [2, 3, 5, 3517] ⟨422041, 19, [(2, 3), (3, 1), (5, 1), (3517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3517
  · decide +kernel

theorem prime_435107 : Nat.Prime 435107 := by
  apply nodeValid_prime [2, 7, 31079] ⟨435107, 2, [(2, 1), (7, 1), (31079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31079
  · decide +kernel

theorem prime_445087 : Nat.Prime 445087 := by
  apply nodeValid_prime [2, 3, 79, 313] ⟨445087, 3, [(2, 1), (3, 2), (79, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_313
  · decide +kernel

theorem prime_534913 : Nat.Prime 534913 := by
  apply nodeValid_prime [2, 3, 7, 199] ⟨534913, 5, [(2, 7), (3, 1), (7, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199
  · decide +kernel

theorem prime_587677 : Nat.Prime 587677 := by
  apply nodeValid_prime [2, 3, 48973] ⟨587677, 2, [(2, 2), (3, 1), (48973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48973
  · decide +kernel

theorem prime_589187 : Nat.Prime 589187 := by
  apply nodeValid_prime [2, 13, 17, 31, 43] ⟨589187, 2, [(2, 1), (13, 1), (17, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_739069 : Nat.Prime 739069 := by
  apply nodeValid_prime [2, 3, 11, 509] ⟨739069, 2, [(2, 2), (3, 1), (11, 2), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_509
  · decide +kernel

theorem prime_857069 : Nat.Prime 857069 := by
  apply nodeValid_prime [2, 37, 5791] ⟨857069, 2, [(2, 2), (37, 1), (5791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_5791
  · decide +kernel

theorem prime_916471 : Nat.Prime 916471 := by
  apply nodeValid_prime [2, 3, 5, 17, 599] ⟨916471, 12, [(2, 1), (3, 2), (5, 1), (17, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_599
  · decide +kernel

theorem prime_971149 : Nat.Prime 971149 := by
  apply nodeValid_prime [2, 3, 80929] ⟨971149, 10, [(2, 2), (3, 1), (80929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80929
  · decide +kernel

theorem prime_1037347 : Nat.Prime 1037347 := by
  apply nodeValid_prime [2, 3, 23, 7517] ⟨1037347, 2, [(2, 1), (3, 1), (23, 1), (7517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_7517
  · decide +kernel

theorem prime_1140257 : Nat.Prime 1140257 := by
  apply nodeValid_prime [2, 13, 2741] ⟨1140257, 3, [(2, 5), (13, 1), (2741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2741
  · decide +kernel

theorem prime_1230461 : Nat.Prime 1230461 := by
  apply nodeValid_prime [2, 5, 7, 11, 17, 47] ⟨1230461, 13, [(2, 2), (5, 1), (7, 1), (11, 1), (17, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_1678129 : Nat.Prime 1678129 := by
  apply nodeValid_prime [2, 3, 34961] ⟨1678129, 7, [(2, 4), (3, 1), (34961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34961
  · decide +kernel

theorem prime_1787603 : Nat.Prime 1787603 := by
  apply nodeValid_prime [2, 157, 5693] ⟨1787603, 2, [(2, 1), (157, 1), (5693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_5693
  · decide +kernel

theorem prime_1800553 : Nat.Prime 1800553 := by
  apply nodeValid_prime [2, 3, 13, 29, 199] ⟨1800553, 10, [(2, 3), (3, 1), (13, 1), (29, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_199
  · decide +kernel

theorem prime_2175857 : Nat.Prime 2175857 := by
  apply nodeValid_prime [2, 239, 569] ⟨2175857, 3, [(2, 4), (239, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_569
  · decide +kernel

theorem prime_2514529 : Nat.Prime 2514529 := by
  apply nodeValid_prime [2, 3, 8731] ⟨2514529, 7, [(2, 5), (3, 2), (8731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8731
  · decide +kernel

theorem prime_2840203 : Nat.Prime 2840203 := by
  apply nodeValid_prime [2, 3, 29, 5441] ⟨2840203, 2, [(2, 1), (3, 2), (29, 1), (5441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_5441
  · decide +kernel

theorem prime_3416011 : Nat.Prime 3416011 := by
  apply nodeValid_prime [2, 3, 5, 13, 19, 461] ⟨3416011, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_461
  · decide +kernel

theorem prime_4043411 : Nat.Prime 4043411 := by
  apply nodeValid_prime [2, 5, 7, 47, 1229] ⟨4043411, 6, [(2, 1), (5, 1), (7, 1), (47, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_1229
  · decide +kernel

theorem prime_4149389 : Nat.Prime 4149389 := by
  apply nodeValid_prime [2, 1037347] ⟨4149389, 2, [(2, 2), (1037347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1037347
  · decide +kernel

theorem prime_4559459 : Nat.Prime 4559459 := by
  apply nodeValid_prime [2, 223, 10223] ⟨4559459, 2, [(2, 1), (223, 1), (10223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_10223
  · decide +kernel

theorem prime_4654421 : Nat.Prime 4654421 := by
  apply nodeValid_prime [2, 5, 409, 569] ⟨4654421, 2, [(2, 2), (5, 1), (409, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
    · exact prime_569
  · decide +kernel

theorem prime_5256623 : Nat.Prime 5256623 := by
  apply nodeValid_prime [2, 7, 53639] ⟨5256623, 7, [(2, 1), (7, 2), (53639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53639
  · decide +kernel

theorem prime_5420057 : Nat.Prime 5420057 := by
  apply nodeValid_prime [2, 37, 18311] ⟨5420057, 3, [(2, 3), (37, 1), (18311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_18311
  · decide +kernel

theorem prime_6073003 : Nat.Prime 6073003 := by
  apply nodeValid_prime [2, 3, 13, 41, 211] ⟨6073003, 5, [(2, 1), (3, 3), (13, 1), (41, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_211
  · decide +kernel

theorem prime_7405639 : Nat.Prime 7405639 := by
  apply nodeValid_prime [2, 3, 397, 3109] ⟨7405639, 3, [(2, 1), (3, 1), (397, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_3109
  · decide +kernel

theorem prime_7408213 : Nat.Prime 7408213 := by
  apply nodeValid_prime [2, 3, 7, 43, 293] ⟨7408213, 2, [(2, 2), (3, 1), (7, 2), (43, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_293
  · decide +kernel

theorem prime_7667729 : Nat.Prime 7667729 := by
  apply nodeValid_prime [2, 113, 4241] ⟨7667729, 3, [(2, 4), (113, 1), (4241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_4241
  · decide +kernel

theorem prime_9452783 : Nat.Prime 9452783 := by
  apply nodeValid_prime [2, 17, 29, 9587] ⟨9452783, 7, [(2, 1), (17, 1), (29, 1), (9587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_9587
  · decide +kernel

theorem prime_9589891 : Nat.Prime 9589891 := by
  apply nodeValid_prime [2, 3, 5, 293, 1091] ⟨9589891, 15, [(2, 1), (3, 1), (5, 1), (293, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
    · exact prime_1091
  · decide +kernel

theorem prime_11279299 : Nat.Prime 11279299 := by
  apply nodeValid_prime [2, 3, 107, 17569] ⟨11279299, 2, [(2, 1), (3, 1), (107, 1), (17569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_17569
  · decide +kernel

theorem prime_12540389 : Nat.Prime 12540389 := by
  apply nodeValid_prime [2, 7, 227, 1973] ⟨12540389, 2, [(2, 2), (7, 1), (227, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
    · exact prime_1973
  · decide +kernel

theorem prime_13240531 : Nat.Prime 13240531 := by
  apply nodeValid_prime [2, 3, 5, 19, 29, 89] ⟨13240531, 2, [(2, 1), (3, 3), (5, 1), (19, 1), (29, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_89
  · decide +kernel

theorem prime_20980403 : Nat.Prime 20980403 := by
  apply nodeValid_prime [2, 173, 60637] ⟨20980403, 2, [(2, 1), (173, 1), (60637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_60637
  · decide +kernel

theorem prime_27655409 : Nat.Prime 27655409 := by
  apply nodeValid_prime [2, 11, 157133] ⟨27655409, 3, [(2, 4), (11, 1), (157133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_157133
  · decide +kernel

theorem prime_27892873 : Nat.Prime 27892873 := by
  apply nodeValid_prime [2, 3, 7, 55343] ⟨27892873, 5, [(2, 3), (3, 2), (7, 1), (55343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_55343
  · decide +kernel

theorem prime_28850287 : Nat.Prime 28850287 := by
  apply nodeValid_prime [2, 3, 1447, 3323] ⟨28850287, 3, [(2, 1), (3, 1), (1447, 1), (3323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1447
    · exact prime_3323
  · decide +kernel

theorem prime_35678521 : Nat.Prime 35678521 := by
  apply nodeValid_prime [2, 3, 5, 23, 31, 139] ⟨35678521, 13, [(2, 3), (3, 2), (5, 1), (23, 1), (31, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_31
    · exact prime_139
  · decide +kernel

theorem prime_44856961 : Nat.Prime 44856961 := by
  apply nodeValid_prime [2, 3, 5, 61, 383] ⟨44856961, 11, [(2, 7), (3, 1), (5, 1), (61, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_383
  · decide +kernel

theorem prime_58175641 : Nat.Prime 58175641 := by
  apply nodeValid_prime [2, 3, 5, 161599] ⟨58175641, 11, [(2, 3), (3, 2), (5, 1), (161599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_161599
  · decide +kernel

theorem prime_63344399 : Nat.Prime 63344399 := by
  apply nodeValid_prime [2, 13, 659, 3697] ⟨63344399, 29, [(2, 1), (13, 1), (659, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_659
    · exact prime_3697
  · decide +kernel

theorem prime_79397039 : Nat.Prime 79397039 := by
  apply nodeValid_prime [2, 7, 17, 271, 1231] ⟨79397039, 7, [(2, 1), (7, 1), (17, 1), (271, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_271
    · exact prime_1231
  · decide +kernel

theorem prime_114868249 : Nat.Prime 114868249 := by
  apply nodeValid_prime [2, 3, 11, 435107] ⟨114868249, 7, [(2, 3), (3, 1), (11, 1), (435107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_435107
  · decide +kernel

theorem prime_133301503 : Nat.Prime 133301503 := by
  apply nodeValid_prime [2, 3, 7405639] ⟨133301503, 6, [(2, 1), (3, 2), (7405639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7405639
  · decide +kernel

theorem prime_164964781 : Nat.Prime 164964781 := by
  apply nodeValid_prime [2, 3, 5, 916471] ⟨164964781, 2, [(2, 2), (3, 2), (5, 1), (916471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_916471
  · decide +kernel

theorem prime_206939321 : Nat.Prime 206939321 := by
  apply nodeValid_prime [2, 5, 7, 739069] ⟨206939321, 3, [(2, 3), (5, 1), (7, 1), (739069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_739069
  · decide +kernel

theorem prime_266695669 : Nat.Prime 266695669 := by
  apply nodeValid_prime [2, 3, 7408213] ⟨266695669, 6, [(2, 2), (3, 2), (7408213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7408213
  · decide +kernel

theorem prime_286988249 : Nat.Prime 286988249 := by
  apply nodeValid_prime [2, 71, 199, 2539] ⟨286988249, 3, [(2, 3), (71, 1), (199, 1), (2539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_199
    · exact prime_2539
  · decide +kernel

theorem prime_356202089 : Nat.Prime 356202089 := by
  apply nodeValid_prime [2, 11, 17, 238103] ⟨356202089, 3, [(2, 3), (11, 1), (17, 1), (238103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_238103
  · decide +kernel

theorem prime_398807581 : Nat.Prime 398807581 := by
  apply nodeValid_prime [2, 3, 5, 23, 288991] ⟨398807581, 11, [(2, 2), (3, 1), (5, 1), (23, 1), (288991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_288991
  · decide +kernel

theorem prime_407353699 : Nat.Prime 407353699 := by
  apply nodeValid_prime [2, 3, 2514529] ⟨407353699, 2, [(2, 1), (3, 4), (2514529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2514529
  · decide +kernel

theorem prime_491372059 : Nat.Prime 491372059 := by
  apply nodeValid_prime [2, 3, 3919, 20897] ⟨491372059, 2, [(2, 1), (3, 1), (3919, 1), (20897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3919
    · exact prime_20897
  · decide +kernel

theorem prime_520325473 : Nat.Prime 520325473 := by
  apply nodeValid_prime [2, 3, 5420057] ⟨520325473, 5, [(2, 5), (3, 1), (5420057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5420057
  · decide +kernel

theorem prime_573976499 : Nat.Prime 573976499 := by
  apply nodeValid_prime [2, 286988249] ⟨573976499, 2, [(2, 1), (286988249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_286988249
  · decide +kernel

theorem prime_728831717 : Nat.Prime 728831717 := by
  apply nodeValid_prime [2, 19, 9589891] ⟨728831717, 2, [(2, 2), (19, 1), (9589891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_9589891
  · decide +kernel

theorem prime_767027333 : Nat.Prime 767027333 := by
  apply nodeValid_prime [2, 109, 173, 10169] ⟨767027333, 2, [(2, 2), (109, 1), (173, 1), (10169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_173
    · exact prime_10169
  · decide +kernel

theorem prime_856884503 : Nat.Prime 856884503 := by
  apply nodeValid_prime [2, 41, 613, 17047] ⟨856884503, 5, [(2, 1), (41, 1), (613, 1), (17047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_613
    · exact prime_17047
  · decide +kernel

theorem prime_1019064797 : Nat.Prime 1019064797 := by
  apply nodeValid_prime [2, 17, 443, 33829] ⟨1019064797, 2, [(2, 2), (17, 1), (443, 1), (33829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_443
    · exact prime_33829
  · decide +kernel

theorem prime_1993822507 : Nat.Prime 1993822507 := by
  apply nodeValid_prime [2, 3, 13, 2840203] ⟨1993822507, 5, [(2, 1), (3, 3), (13, 1), (2840203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2840203
  · decide +kernel

theorem prime_3062701693 : Nat.Prime 3062701693 := by
  apply nodeValid_prime [2, 3, 9452783] ⟨3062701693, 2, [(2, 2), (3, 4), (9452783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9452783
  · decide +kernel

theorem prime_3263785501 : Nat.Prime 3263785501 := by
  apply nodeValid_prime [2, 3, 5, 2175857] ⟨3263785501, 13, [(2, 2), (3, 1), (5, 3), (2175857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2175857
  · decide +kernel

theorem prime_4183930951 : Nat.Prime 4183930951 := by
  apply nodeValid_prime [2, 3, 5, 27892873] ⟨4183930951, 7, [(2, 1), (3, 1), (5, 2), (27892873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27892873
  · decide +kernel

theorem prime_4470453829 : Nat.Prime 4470453829 := by
  apply nodeValid_prime [2, 3, 31, 445087] ⟨4470453829, 2, [(2, 2), (3, 4), (31, 1), (445087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_445087
  · decide +kernel

theorem prime_5443762787 : Nat.Prime 5443762787 := by
  apply nodeValid_prime [2, 7, 11, 89, 397181] ⟨5443762787, 2, [(2, 1), (7, 1), (11, 1), (89, 1), (397181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_89
    · exact prime_397181
  · decide +kernel

theorem prime_5773621639 : Nat.Prime 5773621639 := by
  apply nodeValid_prime [2, 3, 14251, 67523] ⟨5773621639, 3, [(2, 1), (3, 1), (14251, 1), (67523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14251
    · exact prime_67523
  · decide +kernel

theorem prime_12405770903 : Nat.Prime 12405770903 := by
  apply nodeValid_prime [2, 7, 1949, 64951] ⟨12405770903, 7, [(2, 1), (7, 2), (1949, 1), (64951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1949
    · exact prime_64951
  · decide +kernel

theorem prime_13173158423 : Nat.Prime 13173158423 := by
  apply nodeValid_prime [2, 859, 7667729] ⟨13173158423, 5, [(2, 1), (859, 1), (7667729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_859
    · exact prime_7667729
  · decide +kernel

theorem prime_20676284821 : Nat.Prime 20676284821 := by
  apply nodeValid_prime [2, 3, 5, 114868249] ⟨20676284821, 6, [(2, 2), (3, 2), (5, 1), (114868249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_114868249
  · decide +kernel

theorem prime_26346316847 : Nat.Prime 26346316847 := by
  apply nodeValid_prime [2, 13173158423] ⟨26346316847, 5, [(2, 1), (13173158423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13173158423
  · decide +kernel

theorem prime_30571943911 : Nat.Prime 30571943911 := by
  apply nodeValid_prime [2, 3, 5, 1019064797] ⟨30571943911, 3, [(2, 1), (3, 1), (5, 1), (1019064797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1019064797
  · decide +kernel

theorem prime_45940529263 : Nat.Prime 45940529263 := by
  apply nodeValid_prime [2, 3, 37, 206939321] ⟨45940529263, 5, [(2, 1), (3, 1), (37, 1), (206939321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_206939321
  · decide +kernel

theorem prime_46188973547 : Nat.Prime 46188973547 := by
  apply nodeValid_prime [2, 47, 491372059] ⟨46188973547, 2, [(2, 1), (47, 1), (491372059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_491372059
  · decide +kernel

theorem prime_60704638447 : Nat.Prime 60704638447 := by
  apply nodeValid_prime [2, 3, 6029, 1678129] ⟨60704638447, 3, [(2, 1), (3, 1), (6029, 1), (1678129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6029
    · exact prime_1678129
  · decide +kernel

theorem prime_61033881331 : Nat.Prime 61033881331 := by
  apply nodeValid_prime [2, 3, 5, 1151, 589187] ⟨61033881331, 2, [(2, 1), (3, 2), (5, 1), (1151, 1), (589187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1151
    · exact prime_589187
  · decide +kernel

theorem prime_62028856033 : Nat.Prime 62028856033 := by
  apply nodeValid_prime [2, 3, 11, 13, 23, 196453] ⟨62028856033, 10, [(2, 5), (3, 1), (11, 1), (13, 1), (23, 1), (196453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_196453
  · decide +kernel

theorem prime_93544423633 : Nat.Prime 93544423633 := by
  apply nodeValid_prime [2, 3, 11, 2531, 23333] ⟨93544423633, 5, [(2, 4), (3, 2), (11, 1), (2531, 1), (23333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2531
    · exact prime_23333
  · decide +kernel

theorem prime_183762117053 : Nat.Prime 183762117053 := by
  apply nodeValid_prime [2, 45940529263] ⟨183762117053, 2, [(2, 2), (45940529263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_45940529263
  · decide +kernel

theorem prime_361605194371 : Nat.Prime 361605194371 := by
  apply nodeValid_prime [2, 3, 5, 7, 573976499] ⟨361605194371, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (573976499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_573976499
  · decide +kernel

theorem prime_361605260267 : Nat.Prime 361605260267 := by
  apply nodeValid_prime [2, 211, 856884503] ⟨361605260267, 2, [(2, 1), (211, 1), (856884503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_856884503
  · decide +kernel

theorem prime_361605260417 : Nat.Prime 361605260417 := by
  apply nodeValid_prime [2, 827, 3416011] ⟨361605260417, 3, [(2, 7), (827, 1), (3416011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_827
    · exact prime_3416011
  · decide +kernel

theorem prime_362259646381 : Nat.Prime 362259646381 := by
  apply nodeValid_prime [2, 3, 5, 4567, 146891] ⟨362259646381, 2, [(2, 2), (3, 3), (5, 1), (4567, 1), (146891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4567
    · exact prime_146891
  · decide +kernel

theorem prime_362259648901 : Nat.Prime 362259648901 := by
  apply nodeValid_prime [2, 3, 5, 353, 1140257] ⟨362259648901, 2, [(2, 2), (3, 2), (5, 2), (353, 1), (1140257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_353
    · exact prime_1140257
  · decide +kernel

theorem prime_362259648929 : Nat.Prime 362259648929 := by
  apply nodeValid_prime [2, 19, 29, 1697, 12107] ⟨362259648929, 3, [(2, 5), (19, 1), (29, 1), (1697, 1), (12107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_1697
    · exact prime_12107
  · decide +kernel

theorem prime_362914898711 : Nat.Prime 362914898711 := by
  apply nodeValid_prime [2, 5, 7, 13, 398807581] ⟨362914898711, 21, [(2, 1), (5, 1), (7, 1), (13, 1), (398807581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_398807581
  · decide +kernel

theorem prime_362914933891 : Nat.Prime 362914933891 := by
  apply nodeValid_prime [2, 3, 5, 211, 1033, 55501] ⟨362914933891, 2, [(2, 1), (3, 1), (5, 1), (211, 1), (1033, 1), (55501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_211
    · exact prime_1033
    · exact prime_55501
  · decide +kernel

theorem prime_362914934329 : Nat.Prime 362914934329 := by
  apply nodeValid_prime [2, 3, 349, 534913] ⟨362914934329, 7, [(2, 3), (3, 5), (349, 1), (534913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_534913
  · decide +kernel

theorem prime_363570955843 : Nat.Prime 363570955843 := by
  apply nodeValid_prime [2, 3, 79, 767027333] ⟨363570955843, 2, [(2, 1), (3, 1), (79, 1), (767027333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_767027333
  · decide +kernel

theorem prime_363570957889 : Nat.Prime 363570957889 := by
  apply nodeValid_prime [2, 3, 151, 12540389] ⟨363570957889, 7, [(2, 6), (3, 1), (151, 1), (12540389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_12540389
  · decide +kernel

theorem prime_363570958169 : Nat.Prime 363570958169 := by
  apply nodeValid_prime [2, 11, 29, 857, 166237] ⟨363570958169, 3, [(2, 3), (11, 1), (29, 1), (857, 1), (166237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_857
    · exact prime_166237
  · decide +kernel

theorem prime_364227822757 : Nat.Prime 364227822757 := by
  apply nodeValid_prime [2, 3, 7, 317, 4559459] ⟨364227822757, 5, [(2, 2), (3, 2), (7, 1), (317, 1), (4559459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_317
    · exact prime_4559459
  · decide +kernel

theorem prime_364227830683 : Nat.Prime 364227830683 := by
  apply nodeValid_prime [2, 3, 60704638447] ⟨364227830683, 2, [(2, 1), (3, 1), (60704638447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_60704638447
  · decide +kernel

theorem prime_364227831101 : Nat.Prime 364227831101 := by
  apply nodeValid_prime [2, 5, 7, 520325473] ⟨364227831101, 10, [(2, 2), (5, 2), (7, 1), (520325473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_520325473
  · decide +kernel

theorem prime_364885495463 : Nat.Prime 364885495463 := by
  apply nodeValid_prime [2, 45121, 4043411] ⟨364885495463, 5, [(2, 1), (45121, 1), (4043411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_45121
    · exact prime_4043411
  · decide +kernel

theorem prime_364885524361 : Nat.Prime 364885524361 := by
  apply nodeValid_prime [2, 3, 5, 7, 1787603] ⟨364885524361, 11, [(2, 3), (3, 6), (5, 1), (7, 1), (1787603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1787603
  · decide +kernel

theorem prime_364885525153 : Nat.Prime 364885525153 := by
  apply nodeValid_prime [2, 3, 29, 163, 433, 619] ⟨364885525153, 5, [(2, 5), (3, 2), (29, 1), (163, 1), (433, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_163
    · exact prime_433
    · exact prime_619
  · decide +kernel

theorem prime_365543967557 : Nat.Prime 365543967557 := by
  apply nodeValid_prime [2, 1151, 79397039] ⟨365543967557, 2, [(2, 2), (1151, 1), (79397039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1151
    · exact prime_79397039
  · decide +kernel

theorem prime_365543976113 : Nat.Prime 365543976113 := by
  apply nodeValid_prime [2, 7, 3263785501] ⟨365543976113, 3, [(2, 4), (7, 1), (3263785501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3263785501
  · decide +kernel

theorem prime_365543977811 : Nat.Prime 365543977811 := by
  apply nodeValid_prime [2, 5, 11, 17, 139, 173, 739] ⟨365543977811, 2, [(2, 1), (5, 1), (11, 2), (17, 1), (139, 1), (173, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_139
    · exact prime_173
    · exact prime_739
  · decide +kernel

theorem prime_366203249143 : Nat.Prime 366203249143 := by
  apply nodeValid_prime [2, 3, 19, 10093, 318271] ⟨366203249143, 7, [(2, 1), (3, 1), (19, 1), (10093, 1), (318271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_10093
    · exact prime_318271
  · decide +kernel

theorem prime_366203287537 : Nat.Prime 366203287537 := by
  apply nodeValid_prime [2, 3, 18077, 422041] ⟨366203287537, 7, [(2, 4), (3, 1), (18077, 1), (422041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18077
    · exact prime_422041
  · decide +kernel

theorem prime_366203287987 : Nat.Prime 366203287987 := by
  apply nodeValid_prime [2, 3, 61033881331] ⟨366203287987, 11, [(2, 1), (3, 1), (61033881331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61033881331
  · decide +kernel

theorem prime_366863326859 : Nat.Prime 366863326859 := by
  apply nodeValid_prime [2, 7, 1249, 20980403] ⟨366863326859, 2, [(2, 1), (7, 1), (1249, 1), (20980403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1249
    · exact prime_20980403
  · decide +kernel

theorem prime_366863326933 : Nat.Prime 366863326933 := by
  apply nodeValid_prime [2, 3, 30571943911] ⟨366863326933, 5, [(2, 2), (3, 1), (30571943911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30571943911
  · decide +kernel

theorem prime_366863341289 : Nat.Prime 366863341289 := by
  apply nodeValid_prime [2, 23, 1993822507] ⟨366863341289, 3, [(2, 3), (23, 1), (1993822507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1993822507
  · decide +kernel

theorem prime_367524202999 : Nat.Prime 367524202999 := by
  apply nodeValid_prime [2, 3, 967, 63344399] ⟨367524202999, 6, [(2, 1), (3, 1), (967, 1), (63344399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
    · exact prime_63344399
  · decide +kernel

theorem prime_367524203161 : Nat.Prime 367524203161 := by
  apply nodeValid_prime [2, 3, 5, 3062701693] ⟨367524203161, 7, [(2, 3), (3, 1), (5, 1), (3062701693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3062701693
  · decide +kernel

theorem prime_367524234107 : Nat.Prime 367524234107 := by
  apply nodeValid_prime [2, 183762117053] ⟨367524234107, 2, [(2, 1), (183762117053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_183762117053
  · decide +kernel

theorem prime_368185923187 : Nat.Prime 368185923187 := by
  apply nodeValid_prime [2, 3, 49871, 1230461] ⟨368185923187, 2, [(2, 1), (3, 1), (49871, 1), (1230461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_49871
    · exact prime_1230461
  · decide +kernel

theorem prime_368185923689 : Nat.Prime 368185923689 := by
  apply nodeValid_prime [2, 11, 4183930951] ⟨368185923689, 3, [(2, 3), (11, 1), (4183930951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4183930951
  · decide +kernel

theorem prime_368185935889 : Nat.Prime 368185935889 := by
  apply nodeValid_prime [2, 3, 19, 44856961] ⟨368185935889, 31, [(2, 4), (3, 3), (19, 1), (44856961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_44856961
  · decide +kernel

theorem prime_368848435859 : Nat.Prime 368848435859 := by
  apply nodeValid_prime [2, 7, 26346316847] ⟨368848435859, 6, [(2, 1), (7, 1), (26346316847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_26346316847
  · decide +kernel

theorem prime_368848436227 : Nat.Prime 368848436227 := by
  apply nodeValid_prime [2, 3, 29, 223, 1553, 6121] ⟨368848436227, 3, [(2, 1), (3, 1), (29, 1), (223, 1), (1553, 1), (6121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_223
    · exact prime_1553
    · exact prime_6121
  · decide +kernel

theorem prime_368848448443 : Nat.Prime 368848448443 := by
  apply nodeValid_prime [2, 3, 43, 1901, 83561] ⟨368848448443, 2, [(2, 1), (3, 3), (43, 1), (1901, 1), (83561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1901
    · exact prime_83561
  · decide +kernel

theorem prime_369511766317 : Nat.Prime 369511766317 := by
  apply nodeValid_prime [2, 3, 7, 11, 133301503] ⟨369511766317, 6, [(2, 2), (3, 2), (7, 1), (11, 1), (133301503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_133301503
  · decide +kernel

theorem prime_369511784897 : Nat.Prime 369511784897 := by
  apply nodeValid_prime [2, 5773621639] ⟨369511784897, 3, [(2, 6), (5773621639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5773621639
  · decide +kernel

theorem prime_369511788377 : Nat.Prime 369511788377 := by
  apply nodeValid_prime [2, 46188973547] ⟨369511788377, 3, [(2, 3), (46188973547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46188973547
  · decide +kernel

theorem prime_370175869199 : Nat.Prime 370175869199 := by
  apply nodeValid_prime [2, 853, 1301, 166783] ⟨370175869199, 11, [(2, 1), (853, 1), (1301, 1), (166783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_853
    · exact prime_1301
    · exact prime_166783
  · decide +kernel

theorem prime_370175869517 : Nat.Prime 370175869517 := by
  apply nodeValid_prime [2, 17, 5443762787] ⟨370175869517, 2, [(2, 2), (17, 1), (5443762787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_5443762787
  · decide +kernel

theorem prime_370175891209 : Nat.Prime 370175891209 := by
  apply nodeValid_prime [2, 3, 17, 43, 449, 46993] ⟨370175891209, 7, [(2, 3), (3, 1), (17, 1), (43, 1), (449, 1), (46993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_449
    · exact prime_46993
  · decide +kernel

theorem prime_370840792249 : Nat.Prime 370840792249 := by
  apply nodeValid_prime [2, 3, 389, 13240531] ⟨370840792249, 13, [(2, 3), (3, 2), (389, 1), (13240531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_13240531
  · decide +kernel

theorem prime_370840792523 : Nat.Prime 370840792523 := by
  apply nodeValid_prime [2, 17, 967, 11279299] ⟨370840792523, 2, [(2, 1), (17, 1), (967, 1), (11279299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_967
    · exact prime_11279299
  · decide +kernel

theorem prime_370840827689 : Nat.Prime 370840827689 := by
  apply nodeValid_prime [2, 281, 164964781] ⟨370840827689, 3, [(2, 3), (281, 1), (164964781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_164964781
  · decide +kernel

theorem prime_371506573489 : Nat.Prime 371506573489 := by
  apply nodeValid_prime [2, 3, 19, 407353699] ⟨371506573489, 11, [(2, 4), (3, 1), (19, 1), (407353699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_407353699
  · decide +kernel

theorem prime_371506573903 : Nat.Prime 371506573903 := by
  apply nodeValid_prime [2, 3, 11779, 5256623] ⟨371506573903, 3, [(2, 1), (3, 1), (11779, 1), (5256623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11779
    · exact prime_5256623
  · decide +kernel

theorem prime_371506575379 : Nat.Prime 371506575379 := by
  apply nodeValid_prime [2, 3, 53, 251, 4654421] ⟨371506575379, 2, [(2, 1), (3, 1), (53, 1), (251, 1), (4654421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_251
    · exact prime_4654421
  · decide +kernel

theorem prime_372173126779 : Nat.Prime 372173126779 := by
  apply nodeValid_prime [2, 3, 20676284821] ⟨372173126779, 2, [(2, 1), (3, 2), (20676284821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20676284821
  · decide +kernel

theorem prime_372173127091 : Nat.Prime 372173127091 := by
  apply nodeValid_prime [2, 3, 5, 12405770903] ⟨372173127091, 2, [(2, 1), (3, 1), (5, 1), (12405770903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12405770903
  · decide +kernel

theorem prime_372173136199 : Nat.Prime 372173136199 := by
  apply nodeValid_prime [2, 3, 62028856033] ⟨372173136199, 3, [(2, 1), (3, 1), (62028856033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62028856033
  · decide +kernel

theorem prime_372840509711 : Nat.Prime 372840509711 := by
  apply nodeValid_prime [2, 5, 20707, 1800553] ⟨372840509711, 13, [(2, 1), (5, 1), (20707, 1), (1800553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20707
    · exact prime_1800553
  · decide +kernel

theorem prime_372840544451 : Nat.Prime 372840544451 := by
  apply nodeValid_prime [2, 5, 11, 19, 35678521] ⟨372840544451, 10, [(2, 1), (5, 2), (11, 1), (19, 1), (35678521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_35678521
  · decide +kernel

theorem prime_372840545263 : Nat.Prime 372840545263 := by
  apply nodeValid_prime [2, 3, 233, 266695669] ⟨372840545263, 5, [(2, 1), (3, 1), (233, 1), (266695669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_266695669
  · decide +kernel

theorem prime_373508678437 : Nat.Prime 373508678437 := by
  apply nodeValid_prime [2, 3, 89, 16249, 21523] ⟨373508678437, 2, [(2, 2), (3, 1), (89, 1), (16249, 1), (21523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_16249
    · exact prime_21523
  · decide +kernel

theorem prime_373508678737 : Nat.Prime 373508678737 := by
  apply nodeValid_prime [2, 3, 31, 71, 14549] ⟨373508678737, 5, [(2, 4), (3, 6), (31, 1), (71, 1), (14549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_71
    · exact prime_14549
  · decide +kernel

theorem prime_373508695537 : Nat.Prime 373508695537 := by
  apply nodeValid_prime [2, 3, 13241, 587677] ⟨373508695537, 7, [(2, 4), (3, 1), (13241, 1), (587677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13241
    · exact prime_587677
  · decide +kernel

theorem prime_374177683771 : Nat.Prime 374177683771 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 27655409] ⟨374177683771, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (41, 1), (27655409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_27655409
  · decide +kernel

theorem prime_374177683849 : Nat.Prime 374177683849 := by
  apply nodeValid_prime [2, 3, 877, 1741, 10211] ⟨374177683849, 11, [(2, 3), (3, 1), (877, 1), (1741, 1), (10211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_877
    · exact prime_1741
    · exact prime_10211
  · decide +kernel

theorem prime_374177694533 : Nat.Prime 374177694533 := by
  apply nodeValid_prime [2, 93544423633] ⟨374177694533, 2, [(2, 2), (93544423633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_93544423633
  · decide +kernel

theorem prime_374847503483 : Nat.Prime 374847503483 := by
  apply nodeValid_prime [2, 17, 2657, 4149389] ⟨374847503483, 2, [(2, 1), (17, 1), (2657, 1), (4149389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2657
    · exact prime_4149389
  · decide +kernel

theorem prime_374847535651 : Nat.Prime 374847535651 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 2269, 3659] ⟨374847535651, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (43, 1), (2269, 1), (3659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_2269
    · exact prime_3659
  · decide +kernel

theorem prime_374847536933 : Nat.Prime 374847536933 := by
  apply nodeValid_prime [2, 11, 41, 1499, 138617] ⟨374847536933, 2, [(2, 2), (11, 1), (41, 1), (1499, 1), (138617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_1499
    · exact prime_138617
  · decide +kernel

theorem prime_375518067503 : Nat.Prime 375518067503 := by
  apply nodeValid_prime [2, 43, 719, 6073003] ⟨375518067503, 5, [(2, 1), (43, 1), (719, 1), (6073003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_719
    · exact prime_6073003
  · decide +kernel

theorem prime_375518068427 : Nat.Prime 375518068427 := by
  apply nodeValid_prime [2, 193337, 971149] ⟨375518068427, 2, [(2, 1), (193337, 1), (971149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193337
    · exact prime_971149
  · decide +kernel

theorem prime_375518121637 : Nat.Prime 375518121637 := by
  apply nodeValid_prime [2, 3, 7, 4470453829] ⟨375518121637, 2, [(2, 2), (3, 1), (7, 1), (4470453829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4470453829
  · decide +kernel

theorem prime_376189555801 : Nat.Prime 376189555801 := by
  apply nodeValid_prime [2, 3, 5, 17, 6073] ⟨376189555801, 7, [(2, 3), (3, 1), (5, 2), (17, 1), (6073, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_6073
  · decide +kernel

theorem prime_376189560869 : Nat.Prime 376189560869 := by
  apply nodeValid_prime [2, 11, 19, 59, 487, 15661] ⟨376189560869, 2, [(2, 2), (11, 1), (19, 1), (59, 1), (487, 1), (15661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_59
    · exact prime_487
    · exact prime_15661
  · decide +kernel

theorem prime_376189561379 : Nat.Prime 376189561379 := by
  apply nodeValid_prime [2, 23, 79, 593, 174569] ⟨376189561379, 2, [(2, 1), (23, 1), (79, 1), (593, 1), (174569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_79
    · exact prime_593
    · exact prime_174569
  · decide +kernel

theorem prime_376861802399 : Nat.Prime 376861802399 := by
  apply nodeValid_prime [2, 41, 79, 58175641] ⟨376861802399, 11, [(2, 1), (41, 1), (79, 1), (58175641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_79
    · exact prime_58175641
  · decide +kernel

theorem prime_376861809991 : Nat.Prime 376861809991 := by
  apply nodeValid_prime [2, 3, 5, 14657, 857069] ⟨376861809991, 6, [(2, 1), (3, 1), (5, 1), (14657, 1), (857069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14657
    · exact prime_857069
  · decide +kernel

theorem prime_376861810163 : Nat.Prime 376861810163 := by
  apply nodeValid_prime [2, 23, 356202089] ⟨376861810163, 2, [(2, 1), (23, 2), (356202089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_356202089
  · decide +kernel

theorem prime_377534829029 : Nat.Prime 377534829029 := by
  apply nodeValid_prime [2, 7, 70501, 191251] ⟨377534829029, 2, [(2, 2), (7, 1), (70501, 1), (191251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_70501
    · exact prime_191251
  · decide +kernel

theorem prime_377534829407 : Nat.Prime 377534829407 := by
  apply nodeValid_prime [2, 7, 37, 728831717] ⟨377534829407, 7, [(2, 1), (7, 1), (37, 1), (728831717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_728831717
  · decide +kernel

theorem prime_377534855683 : Nat.Prime 377534855683 := by
  apply nodeValid_prime [2, 3, 727, 28850287] ⟨377534855683, 3, [(2, 1), (3, 2), (727, 1), (28850287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_727
    · exact prime_28850287
  · decide +kernel

end Sude.Lucas.Generated
