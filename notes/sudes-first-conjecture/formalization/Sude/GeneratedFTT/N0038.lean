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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2591 : Nat.Prime 2591 := by
  apply nodeValid_prime [2, 5, 7, 37] ⟨2591, 7, [(2, 1), (5, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_6011 : Nat.Prime 6011 := by
  apply nodeValid_prime [2, 5, 601] ⟨6011, 2, [(2, 1), (5, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_601
  · decide +kernel

theorem prime_6143 : Nat.Prime 6143 := by
  apply nodeValid_prime [2, 37, 83] ⟨6143, 5, [(2, 1), (37, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_83
  · decide +kernel

theorem prime_6863 : Nat.Prime 6863 := by
  apply nodeValid_prime [2, 47, 73] ⟨6863, 5, [(2, 1), (47, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_73
  · decide +kernel

theorem prime_10099 : Nat.Prime 10099 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨10099, 2, [(2, 1), (3, 3), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_12323 : Nat.Prime 12323 := by
  apply nodeValid_prime [2, 61, 101] ⟨12323, 2, [(2, 1), (61, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_101
  · decide +kernel

theorem prime_13681 : Nat.Prime 13681 := by
  apply nodeValid_prime [2, 3, 5, 19] ⟨13681, 22, [(2, 4), (3, 2), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_15161 : Nat.Prime 15161 := by
  apply nodeValid_prime [2, 5, 379] ⟨15161, 3, [(2, 3), (5, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_379
  · decide +kernel

theorem prime_16703 : Nat.Prime 16703 := by
  apply nodeValid_prime [2, 7, 1193] ⟨16703, 5, [(2, 1), (7, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1193
  · decide +kernel

theorem prime_16979 : Nat.Prime 16979 := by
  apply nodeValid_prime [2, 13, 653] ⟨16979, 2, [(2, 1), (13, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_653
  · decide +kernel

theorem prime_19763 : Nat.Prime 19763 := by
  apply nodeValid_prime [2, 41, 241] ⟨19763, 2, [(2, 1), (41, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_241
  · decide +kernel

theorem prime_22621 : Nat.Prime 22621 := by
  apply nodeValid_prime [2, 3, 5, 13, 29] ⟨22621, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_22817 : Nat.Prime 22817 := by
  apply nodeValid_prime [2, 23, 31] ⟨22817, 3, [(2, 5), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_23747 : Nat.Prime 23747 := by
  apply nodeValid_prime [2, 31, 383] ⟨23747, 2, [(2, 1), (31, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_383
  · decide +kernel

theorem prime_28411 : Nat.Prime 28411 := by
  apply nodeValid_prime [2, 3, 5, 947] ⟨28411, 2, [(2, 1), (3, 1), (5, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_947
  · decide +kernel

theorem prime_30323 : Nat.Prime 30323 := by
  apply nodeValid_prime [2, 15161] ⟨30323, 2, [(2, 1), (15161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15161
  · decide +kernel

theorem prime_31741 : Nat.Prime 31741 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨31741, 6, [(2, 2), (3, 1), (5, 1), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_32707 : Nat.Prime 32707 := by
  apply nodeValid_prime [2, 3, 23, 79] ⟨32707, 3, [(2, 1), (3, 2), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_36067 : Nat.Prime 36067 := by
  apply nodeValid_prime [2, 3, 6011] ⟨36067, 5, [(2, 1), (3, 1), (6011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6011
  · decide +kernel

theorem prime_41771 : Nat.Prime 41771 := by
  apply nodeValid_prime [2, 5, 4177] ⟨41771, 2, [(2, 1), (5, 1), (4177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4177
  · decide +kernel

theorem prime_43117 : Nat.Prime 43117 := by
  apply nodeValid_prime [2, 3, 3593] ⟨43117, 2, [(2, 2), (3, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3593
  · decide +kernel

theorem prime_45319 : Nat.Prime 45319 := by
  apply nodeValid_prime [2, 3, 7, 13, 83] ⟨45319, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_83
  · decide +kernel

theorem prime_50329 : Nat.Prime 50329 := by
  apply nodeValid_prime [2, 3, 233] ⟨50329, 7, [(2, 3), (3, 3), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
  · decide +kernel

theorem prime_55207 : Nat.Prime 55207 := by
  apply nodeValid_prime [2, 3, 3067] ⟨55207, 5, [(2, 1), (3, 2), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3067
  · decide +kernel

theorem prime_57331 : Nat.Prime 57331 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨57331, 2, [(2, 1), (3, 2), (5, 1), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_58567 : Nat.Prime 58567 := by
  apply nodeValid_prime [2, 3, 43, 227] ⟨58567, 6, [(2, 1), (3, 1), (43, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_227
  · decide +kernel

theorem prime_66041 : Nat.Prime 66041 := by
  apply nodeValid_prime [2, 5, 13, 127] ⟨66041, 3, [(2, 3), (5, 1), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_66457 : Nat.Prime 66457 := by
  apply nodeValid_prime [2, 3, 13, 71] ⟨66457, 5, [(2, 3), (3, 2), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_69539 : Nat.Prime 69539 := by
  apply nodeValid_prime [2, 7, 4967] ⟨69539, 2, [(2, 1), (7, 1), (4967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4967
  · decide +kernel

theorem prime_73141 : Nat.Prime 73141 := by
  apply nodeValid_prime [2, 3, 5, 23, 53] ⟨73141, 7, [(2, 2), (3, 1), (5, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_81001 : Nat.Prime 81001 := by
  apply nodeValid_prime [2, 3, 5] ⟨81001, 11, [(2, 3), (3, 4), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_86243 : Nat.Prime 86243 := by
  apply nodeValid_prime [2, 13, 31, 107] ⟨86243, 2, [(2, 1), (13, 1), (31, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_107
  · decide +kernel

theorem prime_100213 : Nat.Prime 100213 := by
  apply nodeValid_prime [2, 3, 7, 1193] ⟨100213, 2, [(2, 2), (3, 1), (7, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1193
  · decide +kernel

theorem prime_108463 : Nat.Prime 108463 := by
  apply nodeValid_prime [2, 3, 18077] ⟨108463, 5, [(2, 1), (3, 1), (18077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18077
  · decide +kernel

theorem prime_109211 : Nat.Prime 109211 := by
  apply nodeValid_prime [2, 5, 67, 163] ⟨109211, 6, [(2, 1), (5, 1), (67, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_163
  · decide +kernel

theorem prime_110437 : Nat.Prime 110437 := by
  apply nodeValid_prime [2, 3, 9203] ⟨110437, 2, [(2, 2), (3, 1), (9203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9203
  · decide +kernel

theorem prime_139079 : Nat.Prime 139079 := by
  apply nodeValid_prime [2, 69539] ⟨139079, 13, [(2, 1), (69539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_69539
  · decide +kernel

theorem prime_149521 : Nat.Prime 149521 := by
  apply nodeValid_prime [2, 3, 5, 7, 89] ⟨149521, 17, [(2, 4), (3, 1), (5, 1), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_207661 : Nat.Prime 207661 := by
  apply nodeValid_prime [2, 3, 5, 3461] ⟨207661, 2, [(2, 2), (3, 1), (5, 1), (3461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3461
  · decide +kernel

theorem prime_224351 : Nat.Prime 224351 := by
  apply nodeValid_prime [2, 5, 7, 641] ⟨224351, 7, [(2, 1), (5, 2), (7, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_641
  · decide +kernel

theorem prime_275711 : Nat.Prime 275711 := by
  apply nodeValid_prime [2, 5, 79, 349] ⟨275711, 7, [(2, 1), (5, 1), (79, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_349
  · decide +kernel

theorem prime_278149 : Nat.Prime 278149 := by
  apply nodeValid_prime [2, 3, 13, 1783] ⟨278149, 2, [(2, 2), (3, 1), (13, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1783
  · decide +kernel

theorem prime_282773 : Nat.Prime 282773 := by
  apply nodeValid_prime [2, 7, 10099] ⟨282773, 2, [(2, 2), (7, 1), (10099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10099
  · decide +kernel

theorem prime_301051 : Nat.Prime 301051 := by
  apply nodeValid_prime [2, 3, 5, 223] ⟨301051, 7, [(2, 1), (3, 3), (5, 2), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
  · decide +kernel

theorem prime_306703 : Nat.Prime 306703 := by
  apply nodeValid_prime [2, 3, 11, 1549] ⟨306703, 5, [(2, 1), (3, 2), (11, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1549
  · decide +kernel

theorem prime_307537 : Nat.Prime 307537 := by
  apply nodeValid_prime [2, 3, 43, 149] ⟨307537, 5, [(2, 4), (3, 1), (43, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_149
  · decide +kernel

theorem prime_351971 : Nat.Prime 351971 := by
  apply nodeValid_prime [2, 5, 61, 577] ⟨351971, 7, [(2, 1), (5, 1), (61, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_577
  · decide +kernel

theorem prime_352633 : Nat.Prime 352633 := by
  apply nodeValid_prime [2, 3, 7, 2099] ⟨352633, 5, [(2, 3), (3, 1), (7, 1), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2099
  · decide +kernel

theorem prime_367201 : Nat.Prime 367201 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨367201, 11, [(2, 5), (3, 3), (5, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_427447 : Nat.Prime 427447 := by
  apply nodeValid_prime [2, 3, 23747] ⟨427447, 3, [(2, 1), (3, 2), (23747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23747
  · decide +kernel

theorem prime_434243 : Nat.Prime 434243 := by
  apply nodeValid_prime [2, 217121] ⟨434243, 2, [(2, 1), (217121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_217121
  · decide +kernel

theorem prime_463451 : Nat.Prime 463451 := by
  apply nodeValid_prime [2, 5, 13, 23, 31] ⟨463451, 10, [(2, 1), (5, 2), (13, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_517931 : Nat.Prime 517931 := by
  apply nodeValid_prime [2, 5, 7, 151] ⟨517931, 2, [(2, 1), (5, 1), (7, 3), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_151
  · decide +kernel

theorem prime_585671 : Nat.Prime 585671 := by
  apply nodeValid_prime [2, 5, 58567] ⟨585671, 7, [(2, 1), (5, 1), (58567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_58567
  · decide +kernel

theorem prime_926903 : Nat.Prime 926903 := by
  apply nodeValid_prime [2, 463451] ⟨926903, 5, [(2, 1), (463451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_463451
  · decide +kernel

theorem prime_945811 : Nat.Prime 945811 := by
  apply nodeValid_prime [2, 3, 5, 31, 113] ⟨945811, 11, [(2, 1), (3, 3), (5, 1), (31, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_113
  · decide +kernel

theorem prime_1022797 : Nat.Prime 1022797 := by
  apply nodeValid_prime [2, 3, 28411] ⟨1022797, 5, [(2, 2), (3, 2), (28411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28411
  · decide +kernel

theorem prime_1171343 : Nat.Prime 1171343 := by
  apply nodeValid_prime [2, 585671] ⟨1171343, 5, [(2, 1), (585671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_585671
  · decide +kernel

theorem prime_1265977 : Nat.Prime 1265977 := by
  apply nodeValid_prime [2, 3, 5861] ⟨1265977, 5, [(2, 3), (3, 3), (5861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5861
  · decide +kernel

theorem prime_1289287 : Nat.Prime 1289287 := by
  apply nodeValid_prime [2, 3, 41, 1747] ⟨1289287, 3, [(2, 1), (3, 2), (41, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1747
  · decide +kernel

theorem prime_1335527 : Nat.Prime 1335527 := by
  apply nodeValid_prime [2, 733, 911] ⟨1335527, 5, [(2, 1), (733, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_733
    · exact prime_911
  · decide +kernel

theorem prime_1651283 : Nat.Prime 1651283 := by
  apply nodeValid_prime [2, 67, 12323] ⟨1651283, 2, [(2, 1), (67, 1), (12323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_12323
  · decide +kernel

theorem prime_1789481 : Nat.Prime 1789481 := by
  apply nodeValid_prime [2, 5, 7, 11, 83] ⟨1789481, 12, [(2, 3), (5, 1), (7, 2), (11, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_83
  · decide +kernel

theorem prime_1822003 : Nat.Prime 1822003 := by
  apply nodeValid_prime [2, 3, 7, 13, 47, 71] ⟨1822003, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (47, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_47
    · exact prime_71
  · decide +kernel

theorem prime_1853807 : Nat.Prime 1853807 := by
  apply nodeValid_prime [2, 926903] ⟨1853807, 5, [(2, 1), (926903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_926903
  · decide +kernel

theorem prime_2097709 : Nat.Prime 2097709 := by
  apply nodeValid_prime [2, 3, 31, 5639] ⟨2097709, 2, [(2, 2), (3, 1), (31, 1), (5639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_5639
  · decide +kernel

theorem prime_2342687 : Nat.Prime 2342687 := by
  apply nodeValid_prime [2, 1171343] ⟨2342687, 5, [(2, 1), (1171343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1171343
  · decide +kernel

theorem prime_2491933 : Nat.Prime 2491933 := by
  apply nodeValid_prime [2, 3, 207661] ⟨2491933, 2, [(2, 2), (3, 1), (207661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_207661
  · decide +kernel

theorem prime_2642821 : Nat.Prime 2642821 := by
  apply nodeValid_prime [2, 3, 5, 17, 2591] ⟨2642821, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (2591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_2591
  · decide +kernel

theorem prime_3342379 : Nat.Prime 3342379 := by
  apply nodeValid_prime [2, 3, 13, 73, 587] ⟨3342379, 2, [(2, 1), (3, 1), (13, 1), (73, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_587
  · decide +kernel

theorem prime_3442337 : Nat.Prime 3442337 := by
  apply nodeValid_prime [2, 97, 1109] ⟨3442337, 3, [(2, 5), (97, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1109
  · decide +kernel

theorem prime_3526331 : Nat.Prime 3526331 := by
  apply nodeValid_prime [2, 5, 352633] ⟨3526331, 2, [(2, 1), (5, 1), (352633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_352633
  · decide +kernel

theorem prime_3987421 : Nat.Prime 3987421 := by
  apply nodeValid_prime [2, 3, 5, 66457] ⟨3987421, 2, [(2, 2), (3, 1), (5, 1), (66457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_66457
  · decide +kernel

theorem prime_4038319 : Nat.Prime 4038319 := by
  apply nodeValid_prime [2, 3, 224351] ⟨4038319, 3, [(2, 1), (3, 2), (224351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_224351
  · decide +kernel

theorem prime_4498987 : Nat.Prime 4498987 := by
  apply nodeValid_prime [2, 3, 59, 71, 179] ⟨4498987, 2, [(2, 1), (3, 1), (59, 1), (71, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_71
    · exact prime_179
  · decide +kernel

theorem prime_6310181 : Nat.Prime 6310181 := by
  apply nodeValid_prime [2, 5, 53, 5953] ⟨6310181, 2, [(2, 2), (5, 1), (53, 1), (5953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_5953
  · decide +kernel

theorem prime_7223707 : Nat.Prime 7223707 := by
  apply nodeValid_prime [2, 3, 7, 57331] ⟨7223707, 2, [(2, 1), (3, 2), (7, 1), (57331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_57331
  · decide +kernel

theorem prime_7288013 : Nat.Prime 7288013 := by
  apply nodeValid_prime [2, 1822003] ⟨7288013, 2, [(2, 2), (1822003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1822003
  · decide +kernel

theorem prime_7457603 : Nat.Prime 7457603 := by
  apply nodeValid_prime [2, 607, 6143] ⟨7457603, 2, [(2, 1), (607, 1), (6143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_607
    · exact prime_6143
  · decide +kernel

theorem prime_7852811 : Nat.Prime 7852811 := by
  apply nodeValid_prime [2, 5, 7, 17, 6599] ⟨7852811, 2, [(2, 1), (5, 1), (7, 1), (17, 1), (6599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_6599
  · decide +kernel

theorem prime_8025389 : Nat.Prime 8025389 := by
  apply nodeValid_prime [2, 7, 443, 647] ⟨8025389, 2, [(2, 2), (7, 1), (443, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_443
    · exact prime_647
  · decide +kernel

theorem prime_8588651 : Nat.Prime 8588651 := by
  apply nodeValid_prime [2, 5, 7, 53, 463] ⟨8588651, 2, [(2, 1), (5, 2), (7, 1), (53, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_463
  · decide +kernel

theorem prime_14830457 : Nat.Prime 14830457 := by
  apply nodeValid_prime [2, 1853807] ⟨14830457, 3, [(2, 3), (1853807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1853807
  · decide +kernel

theorem prime_17162819 : Nat.Prime 17162819 := by
  apply nodeValid_prime [2, 283, 30323] ⟨17162819, 2, [(2, 1), (283, 1), (30323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_30323
  · decide +kernel

theorem prime_18111031 : Nat.Prime 18111031 := by
  apply nodeValid_prime [2, 3, 5, 7, 86243] ⟨18111031, 30, [(2, 1), (3, 1), (5, 1), (7, 1), (86243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_86243
  · decide +kernel

theorem prime_18697379 : Nat.Prime 18697379 := by
  apply nodeValid_prime [2, 7, 1335527] ⟨18697379, 2, [(2, 1), (7, 1), (1335527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1335527
  · decide +kernel

theorem prime_24386563 : Nat.Prime 24386563 := by
  apply nodeValid_prime [2, 3, 83, 5441] ⟨24386563, 5, [(2, 1), (3, 3), (83, 1), (5441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_5441
  · decide +kernel

theorem prime_26814617 : Nat.Prime 26814617 := by
  apply nodeValid_prime [2, 677, 4951] ⟨26814617, 3, [(2, 3), (677, 1), (4951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_677
    · exact prime_4951
  · decide +kernel

theorem prime_28366343 : Nat.Prime 28366343 := by
  apply nodeValid_prime [2, 41, 53, 61, 107] ⟨28366343, 5, [(2, 1), (41, 1), (53, 1), (61, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_53
    · exact prime_61
    · exact prime_107
  · decide +kernel

theorem prime_40725631 : Nat.Prime 40725631 := by
  apply nodeValid_prime [2, 3, 5, 11, 31, 1327] ⟨40725631, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (31, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_1327
  · decide +kernel

theorem prime_47934671 : Nat.Prime 47934671 := by
  apply nodeValid_prime [2, 5, 7, 691, 991] ⟨47934671, 7, [(2, 1), (5, 1), (7, 1), (691, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_691
    · exact prime_991
  · decide +kernel

theorem prime_48377051 : Nat.Prime 48377051 := by
  apply nodeValid_prime [2, 5, 23, 31, 59] ⟨48377051, 2, [(2, 1), (5, 2), (23, 2), (31, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_31
    · exact prime_59
  · decide +kernel

theorem prime_48405881 : Nat.Prime 48405881 := by
  apply nodeValid_prime [2, 5, 31, 103, 379] ⟨48405881, 3, [(2, 3), (5, 1), (31, 1), (103, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_103
    · exact prime_379
  · decide +kernel

theorem prime_52488649 : Nat.Prime 52488649 := by
  apply nodeValid_prime [2, 3, 81001] ⟨52488649, 7, [(2, 3), (3, 4), (81001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_81001
  · decide +kernel

theorem prime_57345611 : Nat.Prime 57345611 := by
  apply nodeValid_prime [2, 5, 7, 19, 43117] ⟨57345611, 6, [(2, 1), (5, 1), (7, 1), (19, 1), (43117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_43117
  · decide +kernel

theorem prime_61721789 : Nat.Prime 61721789 := by
  apply nodeValid_prime [2, 23, 59, 83, 137] ⟨61721789, 2, [(2, 2), (23, 1), (59, 1), (83, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
    · exact prime_83
    · exact prime_137
  · decide +kernel

theorem prime_62822489 : Nat.Prime 62822489 := by
  apply nodeValid_prime [2, 7852811] ⟨62822489, 3, [(2, 3), (7852811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7852811
  · decide +kernel

theorem prime_80951089 : Nat.Prime 80951089 := by
  apply nodeValid_prime [2, 3, 487, 3463] ⟨80951089, 11, [(2, 4), (3, 1), (487, 1), (3463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
    · exact prime_3463
  · decide +kernel

theorem prime_86100587 : Nat.Prime 86100587 := by
  apply nodeValid_prime [2, 11, 13, 301051] ⟨86100587, 2, [(2, 1), (11, 1), (13, 1), (301051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_301051
  · decide +kernel

theorem prime_96811763 : Nat.Prime 96811763 := by
  apply nodeValid_prime [2, 48405881] ⟨96811763, 2, [(2, 1), (48405881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48405881
  · decide +kernel

theorem prime_129474977 : Nat.Prime 129474977 := by
  apply nodeValid_prime [2, 127, 31859] ⟨129474977, 3, [(2, 5), (127, 1), (31859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_31859
  · decide +kernel

theorem prime_196842911 : Nat.Prime 196842911 := by
  apply nodeValid_prime [2, 5, 11, 1789481] ⟨196842911, 11, [(2, 1), (5, 1), (11, 1), (1789481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1789481
  · decide +kernel

theorem prime_262549613 : Nat.Prime 262549613 := by
  apply nodeValid_prime [2, 13, 61, 6367] ⟨262549613, 2, [(2, 2), (13, 2), (61, 1), (6367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_61
    · exact prime_6367
  · decide +kernel

theorem prime_347750981 : Nat.Prime 347750981 := by
  apply nodeValid_prime [2, 5, 17, 1022797] ⟨347750981, 2, [(2, 2), (5, 1), (17, 1), (1022797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1022797
  · decide +kernel

theorem prime_452561909 : Nat.Prime 452561909 := by
  apply nodeValid_prime [2, 1129, 100213] ⟨452561909, 2, [(2, 2), (1129, 1), (100213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1129
    · exact prime_100213
  · decide +kernel

theorem prime_461248303 : Nat.Prime 461248303 := by
  apply nodeValid_prime [2, 3, 23, 3342379] ⟨461248303, 3, [(2, 1), (3, 1), (23, 1), (3342379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3342379
  · decide +kernel

theorem prime_648780383 : Nat.Prime 648780383 := by
  apply nodeValid_prime [2, 131, 181, 13681] ⟨648780383, 5, [(2, 1), (131, 1), (181, 1), (13681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_181
    · exact prime_13681
  · decide +kernel

theorem prime_653331557 : Nat.Prime 653331557 := by
  apply nodeValid_prime [2, 17, 41, 89, 2633] ⟨653331557, 2, [(2, 2), (17, 1), (41, 1), (89, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_89
    · exact prime_2633
  · decide +kernel

theorem prime_655057939 : Nat.Prime 655057939 := by
  apply nodeValid_prime [2, 3, 149, 853, 859] ⟨655057939, 2, [(2, 1), (3, 1), (149, 1), (853, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_853
    · exact prime_859
  · decide +kernel

theorem prime_740661469 : Nat.Prime 740661469 := by
  apply nodeValid_prime [2, 3, 61721789] ⟨740661469, 2, [(2, 2), (3, 1), (61721789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61721789
  · decide +kernel

theorem prime_756211433 : Nat.Prime 756211433 := by
  apply nodeValid_prime [2, 4783, 19763] ⟨756211433, 3, [(2, 3), (4783, 1), (19763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4783
    · exact prime_19763
  · decide +kernel

theorem prime_790633309 : Nat.Prime 790633309 := by
  apply nodeValid_prime [2, 3, 233, 282773] ⟨790633309, 2, [(2, 2), (3, 1), (233, 1), (282773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_282773
  · decide +kernel

theorem prime_792219277 : Nat.Prime 792219277 := by
  apply nodeValid_prime [2, 3, 167, 313, 421] ⟨792219277, 6, [(2, 2), (3, 2), (167, 1), (313, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_313
    · exact prime_421
  · decide +kernel

theorem prime_905123819 : Nat.Prime 905123819 := by
  apply nodeValid_prime [2, 452561909] ⟨905123819, 2, [(2, 1), (452561909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_452561909
  · decide +kernel

theorem prime_997474589 : Nat.Prime 997474589 := by
  apply nodeValid_prime [2, 11, 163, 139079] ⟨997474589, 2, [(2, 2), (11, 1), (163, 1), (139079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_163
    · exact prime_139079
  · decide +kernel

theorem prime_1136321449 : Nat.Prime 1136321449 := by
  apply nodeValid_prime [2, 3, 19, 2491933] ⟨1136321449, 22, [(2, 3), (3, 1), (19, 1), (2491933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2491933
  · decide +kernel

theorem prime_1810247639 : Nat.Prime 1810247639 := by
  apply nodeValid_prime [2, 905123819] ⟨1810247639, 7, [(2, 1), (905123819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_905123819
  · decide +kernel

theorem prime_2127060239 : Nat.Prime 2127060239 := by
  apply nodeValid_prime [2, 41, 1553, 16703] ⟨2127060239, 13, [(2, 1), (41, 1), (1553, 1), (16703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1553
    · exact prime_16703
  · decide +kernel

theorem prime_2370997693 : Nat.Prime 2370997693 := by
  apply nodeValid_prime [2, 3, 7, 41, 32783] ⟨2370997693, 2, [(2, 2), (3, 2), (7, 2), (41, 1), (32783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_32783
  · decide +kernel

theorem prime_3442752041 : Nat.Prime 3442752041 := by
  apply nodeValid_prime [2, 5, 7, 13, 945811] ⟨3442752041, 3, [(2, 3), (5, 1), (7, 1), (13, 1), (945811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_945811
  · decide +kernel

theorem prime_3669140677 : Nat.Prime 3669140677 := by
  apply nodeValid_prime [2, 3, 41, 7457603] ⟨3669140677, 5, [(2, 2), (3, 1), (41, 1), (7457603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_7457603
  · decide +kernel

theorem prime_3919989343 : Nat.Prime 3919989343 := by
  apply nodeValid_prime [2, 3, 653331557] ⟨3919989343, 3, [(2, 1), (3, 1), (653331557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653331557
  · decide +kernel

theorem prime_5254500239 : Nat.Prime 5254500239 := by
  apply nodeValid_prime [2, 13, 733, 275711] ⟨5254500239, 7, [(2, 1), (13, 1), (733, 1), (275711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_733
    · exact prime_275711
  · decide +kernel

theorem prime_7368181141 : Nat.Prime 7368181141 := by
  apply nodeValid_prime [2, 3, 5, 17, 7223707] ⟨7368181141, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (7223707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_7223707
  · decide +kernel

theorem prime_11467628413 : Nat.Prime 11467628413 := by
  apply nodeValid_prime [2, 3, 271, 3526331] ⟨11467628413, 29, [(2, 2), (3, 1), (271, 1), (3526331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_3526331
  · decide +kernel

theorem prime_17387316409 : Nat.Prime 17387316409 := by
  apply nodeValid_prime [2, 3, 7, 11, 41, 32783] ⟨17387316409, 13, [(2, 3), (3, 1), (7, 2), (11, 1), (41, 1), (32783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_41
    · exact prime_32783
  · decide +kernel

theorem prime_19646021807 : Nat.Prime 19646021807 := by
  apply nodeValid_prime [2, 22621, 434243] ⟨19646021807, 5, [(2, 1), (22621, 1), (434243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_22621
    · exact prime_434243
  · decide +kernel

theorem prime_23519936059 : Nat.Prime 23519936059 := by
  apply nodeValid_prime [2, 3, 3919989343] ⟨23519936059, 3, [(2, 1), (3, 1), (3919989343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3919989343
  · decide +kernel

theorem prime_84995068547 : Nat.Prime 84995068547 := by
  apply nodeValid_prime [2, 557, 8161, 9349] ⟨84995068547, 2, [(2, 1), (557, 1), (8161, 1), (9349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_557
    · exact prime_8161
    · exact prime_9349
  · decide +kernel

theorem prime_127286265553 : Nat.Prime 127286265553 := by
  apply nodeValid_prime [2, 3, 47, 3323, 16979] ⟨127286265553, 10, [(2, 4), (3, 1), (47, 1), (3323, 1), (16979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_3323
    · exact prime_16979
  · decide +kernel

theorem prime_256225820261 : Nat.Prime 256225820261 := by
  apply nodeValid_prime [2, 5, 41771, 306703] ⟨256225820261, 2, [(2, 2), (5, 1), (41771, 1), (306703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41771
    · exact prime_306703
  · decide +kernel

theorem prime_259554101693 : Nat.Prime 259554101693 := by
  apply nodeValid_prime [2, 50329, 1289287] ⟨259554101693, 2, [(2, 2), (50329, 1), (1289287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_50329
    · exact prime_1289287
  · decide +kernel

theorem prime_264601238519 : Nat.Prime 264601238519 := by
  apply nodeValid_prime [2, 167, 792219277] ⟨264601238519, 7, [(2, 1), (167, 1), (792219277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_792219277
  · decide +kernel

theorem prime_509145062213 : Nat.Prime 509145062213 := by
  apply nodeValid_prime [2, 127286265553] ⟨509145062213, 2, [(2, 2), (127286265553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_127286265553
  · decide +kernel

theorem prime_509145062267 : Nat.Prime 509145062267 := by
  apply nodeValid_prime [2, 173, 13567, 108463] ⟨509145062267, 2, [(2, 1), (173, 1), (13567, 1), (108463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_13567
    · exact prime_108463
  · decide +kernel

theorem prime_509145084697 : Nat.Prime 509145084697 := by
  apply nodeValid_prime [2, 3, 53, 281, 541, 2633] ⟨509145084697, 5, [(2, 3), (3, 1), (53, 1), (281, 1), (541, 1), (2633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_281
    · exact prime_541
    · exact prime_2633
  · decide +kernel

theorem prime_509970356377 : Nat.Prime 509970356377 := by
  apply nodeValid_prime [2, 3, 13, 36067, 45319] ⟨509970356377, 7, [(2, 3), (3, 1), (13, 1), (36067, 1), (45319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_36067
    · exact prime_45319
  · decide +kernel

theorem prime_509970410899 : Nat.Prime 509970410899 := by
  apply nodeValid_prime [2, 3, 13, 19, 18111031] ⟨509970410899, 2, [(2, 1), (3, 1), (13, 1), (19, 2), (18111031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_18111031
  · decide +kernel

theorem prime_509970411283 : Nat.Prime 509970411283 := by
  apply nodeValid_prime [2, 3, 84995068547] ⟨509970411283, 2, [(2, 1), (3, 1), (84995068547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_84995068547
  · decide +kernel

theorem prime_510796531589 : Nat.Prime 510796531589 := by
  apply nodeValid_prime [2, 7, 59, 6310181] ⟨510796531589, 2, [(2, 2), (7, 3), (59, 1), (6310181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_6310181
  · decide +kernel

theorem prime_510796566983 : Nat.Prime 510796566983 := by
  apply nodeValid_prime [2, 13, 19646021807] ⟨510796566983, 5, [(2, 1), (13, 1), (19646021807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19646021807
  · decide +kernel

theorem prime_510796568351 : Nat.Prime 510796568351 := by
  apply nodeValid_prime [2, 5, 23, 233, 431, 4423] ⟨510796568351, 17, [(2, 1), (5, 2), (23, 1), (233, 1), (431, 1), (4423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_233
    · exact prime_431
    · exact prime_4423
  · decide +kernel

theorem prime_511623617023 : Nat.Prime 511623617023 := by
  apply nodeValid_prime [2, 3, 7, 2459, 1651283] ⟨511623617023, 5, [(2, 1), (3, 2), (7, 1), (2459, 1), (1651283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2459
    · exact prime_1651283
  · decide +kernel

theorem prime_511623634391 : Nat.Prime 511623634391 := by
  apply nodeValid_prime [2, 5, 11, 271, 17162819] ⟨511623634391, 7, [(2, 1), (5, 1), (11, 1), (271, 1), (17162819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_271
    · exact prime_17162819
  · decide +kernel

theorem prime_511623635513 : Nat.Prime 511623635513 := by
  apply nodeValid_prime [2, 11, 29, 2741, 73141] ⟨511623635513, 3, [(2, 3), (11, 1), (29, 1), (2741, 1), (73141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_2741
    · exact prime_73141
  · decide +kernel

theorem prime_512451611179 : Nat.Prime 512451611179 := by
  apply nodeValid_prime [2, 3, 13, 443, 14830457] ⟨512451611179, 3, [(2, 1), (3, 1), (13, 1), (443, 1), (14830457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_443
    · exact prime_14830457
  · decide +kernel

theorem prime_512451640523 : Nat.Prime 512451640523 := by
  apply nodeValid_prime [2, 256225820261] ⟨512451640523, 2, [(2, 1), (256225820261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_256225820261
  · decide +kernel

theorem prime_512451640651 : Nat.Prime 512451640651 := by
  apply nodeValid_prime [2, 3, 5, 67, 1559, 32707] ⟨512451640651, 2, [(2, 1), (3, 1), (5, 2), (67, 1), (1559, 1), (32707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_1559
    · exact prime_32707
  · decide +kernel

theorem prime_513280447957 : Nat.Prime 513280447957 := by
  apply nodeValid_prime [2, 3, 41, 347750981] ⟨513280447957, 5, [(2, 2), (3, 2), (41, 1), (347750981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_347750981
  · decide +kernel

theorem prime_513280448309 : Nat.Prime 513280448309 := by
  apply nodeValid_prime [2, 6863, 18697379] ⟨513280448309, 2, [(2, 2), (6863, 1), (18697379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6863
    · exact prime_18697379
  · decide +kernel

theorem prime_513280511111 : Nat.Prime 513280511111 := by
  apply nodeValid_prime [2, 5, 1061, 48377051] ⟨513280511111, 7, [(2, 1), (5, 1), (1061, 1), (48377051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1061
    · exact prime_48377051
  · decide +kernel

theorem prime_514110315253 : Nat.Prime 514110315253 := by
  apply nodeValid_prime [2, 3, 103, 4038319] ⟨514110315253, 2, [(2, 2), (3, 1), (103, 2), (4038319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_4038319
  · decide +kernel

theorem prime_514110329081 : Nat.Prime 514110329081 := by
  apply nodeValid_prime [2, 5, 47, 241, 491, 2311] ⟨514110329081, 3, [(2, 3), (5, 1), (47, 1), (241, 1), (491, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_241
    · exact prime_491
    · exact prime_2311
  · decide +kernel

theorem prime_514110329477 : Nat.Prime 514110329477 := by
  apply nodeValid_prime [2, 71, 1810247639] ⟨514110329477, 2, [(2, 2), (71, 1), (1810247639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1810247639
  · decide +kernel

theorem prime_514941023423 : Nat.Prime 514941023423 := by
  apply nodeValid_prime [2, 7, 5254500239] ⟨514941023423, 5, [(2, 1), (7, 2), (5254500239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5254500239
  · decide +kernel

theorem prime_514941055177 : Nat.Prime 514941055177 := by
  apply nodeValid_prime [2, 3, 109, 196842911] ⟨514941055177, 5, [(2, 3), (3, 1), (109, 1), (196842911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_196842911
  · decide +kernel

theorem prime_514941059797 : Nat.Prime 514941059797 := by
  apply nodeValid_prime [2, 3, 5347, 8025389] ⟨514941059797, 2, [(2, 2), (3, 1), (5347, 1), (8025389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5347
    · exact prime_8025389
  · decide +kernel

theorem prime_515772634691 : Nat.Prime 515772634691 := by
  apply nodeValid_prime [2, 5, 821, 62822489] ⟨515772634691, 6, [(2, 1), (5, 1), (821, 1), (62822489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_821
    · exact prime_62822489
  · decide +kernel

theorem prime_515772679871 : Nat.Prime 515772679871 := by
  apply nodeValid_prime [2, 5, 7, 7368181141] ⟨515772679871, 7, [(2, 1), (5, 1), (7, 1), (7368181141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7368181141
  · decide +kernel

theorem prime_515772680011 : Nat.Prime 515772680011 := by
  apply nodeValid_prime [2, 3, 5, 7, 337, 7288013] ⟨515772680011, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (337, 1), (7288013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_337
    · exact prime_7288013
  · decide +kernel

theorem prime_516605094631 : Nat.Prime 516605094631 := by
  apply nodeValid_prime [2, 3, 5, 313, 3541, 5179] ⟨516605094631, 3, [(2, 1), (3, 2), (5, 1), (313, 1), (3541, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_313
    · exact prime_3541
    · exact prime_5179
  · decide +kernel

theorem prime_516605096641 : Nat.Prime 516605096641 := by
  apply nodeValid_prime [2, 3, 5, 1039, 517931] ⟨516605096641, 22, [(2, 6), (3, 1), (5, 1), (1039, 1), (517931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1039
    · exact prime_517931
  · decide +kernel

theorem prime_516605158231 : Nat.Prime 516605158231 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 129474977] ⟨516605158231, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (129474977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_129474977
  · decide +kernel

theorem prime_517438593299 : Nat.Prime 517438593299 := by
  apply nodeValid_prime [2, 11, 23519936059] ⟨517438593299, 2, [(2, 1), (11, 1), (23519936059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23519936059
  · decide +kernel

theorem prime_517438648439 : Nat.Prime 517438648439 := by
  apply nodeValid_prime [2, 110437, 2342687] ⟨517438648439, 11, [(2, 1), (110437, 1), (2342687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_110437
    · exact prime_2342687
  · decide +kernel

theorem prime_517438648901 : Nat.Prime 517438648901 := by
  apply nodeValid_prime [2, 5, 19, 4933, 55207] ⟨517438648901, 2, [(2, 2), (5, 2), (19, 1), (4933, 1), (55207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_4933
    · exact prime_55207
  · decide +kernel

theorem prime_518272917377 : Nat.Prime 518272917377 := by
  apply nodeValid_prime [2, 151, 26814617] ⟨518272917377, 3, [(2, 7), (151, 1), (26814617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_26814617
  · decide +kernel

theorem prime_518272920227 : Nat.Prime 518272920227 := by
  apply nodeValid_prime [2, 4937, 52488649] ⟨518272920227, 2, [(2, 1), (4937, 1), (52488649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4937
    · exact prime_52488649
  · decide +kernel

theorem prime_518272936063 : Nat.Prime 518272936063 := by
  apply nodeValid_prime [2, 3, 7, 47, 262549613] ⟨518272936063, 3, [(2, 1), (3, 1), (7, 1), (47, 1), (262549613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_262549613
  · decide +kernel

theorem prime_519108186463 : Nat.Prime 519108186463 := by
  apply nodeValid_prime [2, 3, 19, 1723, 2642821] ⟨519108186463, 5, [(2, 1), (3, 1), (19, 1), (1723, 1), (2642821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1723
    · exact prime_2642821
  · decide +kernel

theorem prime_519108203387 : Nat.Prime 519108203387 := by
  apply nodeValid_prime [2, 259554101693] ⟨519108203387, 2, [(2, 1), (259554101693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_259554101693
  · decide +kernel

theorem prime_519108203969 : Nat.Prime 519108203969 := by
  apply nodeValid_prime [2, 17, 3191, 149521] ⟨519108203969, 3, [(2, 6), (17, 1), (3191, 1), (149521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3191
    · exact prime_149521
  · decide +kernel

theorem prime_519944349763 : Nat.Prime 519944349763 := by
  apply nodeValid_prime [2, 3, 22817, 1265977] ⟨519944349763, 2, [(2, 1), (3, 2), (22817, 1), (1265977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22817
    · exact prime_1265977
  · decide +kernel

theorem prime_519944349829 : Nat.Prime 519944349829 := by
  apply nodeValid_prime [2, 3, 41, 307, 3442337] ⟨519944349829, 10, [(2, 2), (3, 1), (41, 1), (307, 1), (3442337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_307
    · exact prime_3442337
  · decide +kernel

theorem prime_519944351239 : Nat.Prime 519944351239 := by
  apply nodeValid_prime [2, 3, 13, 740661469] ⟨519944351239, 3, [(2, 1), (3, 3), (13, 1), (740661469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_740661469
  · decide +kernel

theorem prime_520781431759 : Nat.Prime 520781431759 := by
  apply nodeValid_prime [2, 3, 7, 23, 257, 2097709] ⟨520781431759, 6, [(2, 1), (3, 1), (7, 1), (23, 1), (257, 1), (2097709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_257
    · exact prime_2097709
  · decide +kernel

theorem prime_520781442037 : Nat.Prime 520781442037 := by
  apply nodeValid_prime [2, 3, 31, 163, 8588651] ⟨520781442037, 2, [(2, 2), (3, 1), (31, 1), (163, 1), (8588651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_163
    · exact prime_8588651
  · decide +kernel

theorem prime_520781443057 : Nat.Prime 520781443057 := by
  apply nodeValid_prime [2, 3, 7, 41, 397, 31741] ⟨520781443057, 5, [(2, 4), (3, 2), (7, 1), (41, 1), (397, 1), (31741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_397
    · exact prime_31741
  · decide +kernel

theorem prime_521619427933 : Nat.Prime 521619427933 := by
  apply nodeValid_prime [2, 3, 67, 648780383] ⟨521619427933, 2, [(2, 2), (3, 1), (67, 1), (648780383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_648780383
  · decide +kernel

theorem prime_521619492271 : Nat.Prime 521619492271 := by
  apply nodeValid_prime [2, 3, 5, 17387316409] ⟨521619492271, 11, [(2, 1), (3, 1), (5, 1), (17387316409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17387316409
  · decide +kernel

theorem prime_521619492461 : Nat.Prime 521619492461 := by
  apply nodeValid_prime [2, 5, 11, 2370997693] ⟨521619492461, 2, [(2, 2), (5, 1), (11, 1), (2370997693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2370997693
  · decide +kernel

theorem prime_522458328407 : Nat.Prime 522458328407 := by
  apply nodeValid_prime [2, 7, 461, 80951089] ⟨522458328407, 5, [(2, 1), (7, 1), (461, 1), (80951089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_461
    · exact prime_80951089
  · decide +kernel

theorem prime_522458361917 : Nat.Prime 522458361917 := by
  apply nodeValid_prime [2, 37, 41, 86100587] ⟨522458361917, 2, [(2, 2), (37, 1), (41, 1), (86100587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_41
    · exact prime_86100587
  · decide +kernel

theorem prime_522458362337 : Nat.Prime 522458362337 := by
  apply nodeValid_prime [2, 19, 191, 4498987] ⟨522458362337, 3, [(2, 5), (19, 1), (191, 1), (4498987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_191
    · exact prime_4498987
  · decide +kernel

theorem prime_523298145101 : Nat.Prime 523298145101 := by
  apply nodeValid_prime [2, 5, 14251, 367201] ⟨523298145101, 2, [(2, 2), (5, 2), (14251, 1), (367201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14251
    · exact prime_367201
  · decide +kernel

theorem prime_523298310233 : Nat.Prime 523298310233 := by
  apply nodeValid_prime [2, 19, 3442752041] ⟨523298310233, 3, [(2, 3), (19, 1), (3442752041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_3442752041
  · decide +kernel

theorem prime_523298311637 : Nat.Prime 523298311637 := by
  apply nodeValid_prime [2, 173, 756211433] ⟨523298311637, 2, [(2, 2), (173, 1), (756211433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_756211433
  · decide +kernel

theorem prime_524138870971 : Nat.Prime 524138870971 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 40725631] ⟨524138870971, 11, [(2, 1), (3, 2), (5, 1), (11, 1), (13, 1), (40725631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_40725631
  · decide +kernel

theorem prime_524138884541 : Nat.Prime 524138884541 := by
  apply nodeValid_prime [2, 5, 457, 57345611] ⟨524138884541, 2, [(2, 2), (5, 1), (457, 1), (57345611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_457
    · exact prime_57345611
  · decide +kernel

theorem prime_524138884883 : Nat.Prime 524138884883 := by
  apply nodeValid_prime [2, 2707, 96811763] ⟨524138884883, 2, [(2, 1), (2707, 1), (96811763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2707
    · exact prime_96811763
  · decide +kernel

theorem prime_524980509439 : Nat.Prime 524980509439 := by
  apply nodeValid_prime [2, 3, 7, 11, 1136321449] ⟨524980509439, 6, [(2, 1), (3, 1), (7, 1), (11, 1), (1136321449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1136321449
  · decide +kernel

theorem prime_524980516793 : Nat.Prime 524980516793 := by
  apply nodeValid_prime [2, 37, 47934671] ⟨524980516793, 3, [(2, 3), (37, 2), (47934671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_47934671
  · decide +kernel

theorem prime_524980517177 : Nat.Prime 524980517177 := by
  apply nodeValid_prime [2, 83, 790633309] ⟨524980517177, 3, [(2, 3), (83, 1), (790633309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_790633309
  · decide +kernel

theorem prime_525823065421 : Nat.Prime 525823065421 := by
  apply nodeValid_prime [2, 3, 5, 19, 461248303] ⟨525823065421, 7, [(2, 2), (3, 1), (5, 1), (19, 1), (461248303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_461248303
  · decide +kernel

theorem prime_525823071407 : Nat.Prime 525823071407 := by
  apply nodeValid_prime [2, 10781, 24386563] ⟨525823071407, 5, [(2, 1), (10781, 1), (24386563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10781
    · exact prime_24386563
  · decide +kernel

theorem prime_525823072157 : Nat.Prime 525823072157 := by
  apply nodeValid_prime [2, 307537, 427447] ⟨525823072157, 2, [(2, 2), (307537, 1), (427447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307537
    · exact prime_427447
  · decide +kernel

theorem prime_526666540523 : Nat.Prime 526666540523 := by
  apply nodeValid_prime [2, 66041, 3987421] ⟨526666540523, 2, [(2, 1), (66041, 1), (3987421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_66041
    · exact prime_3987421
  · decide +kernel

theorem prime_526666582957 : Nat.Prime 526666582957 := by
  apply nodeValid_prime [2, 3, 67, 655057939] ⟨526666582957, 2, [(2, 2), (3, 1), (67, 1), (655057939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_655057939
  · decide +kernel

theorem prime_526666582993 : Nat.Prime 526666582993 := by
  apply nodeValid_prime [2, 3, 11, 997474589] ⟨526666582993, 10, [(2, 4), (3, 1), (11, 1), (997474589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_997474589
  · decide +kernel

theorem prime_527510906999 : Nat.Prime 527510906999 := by
  apply nodeValid_prime [2, 23, 11467628413] ⟨527510906999, 13, [(2, 1), (23, 1), (11467628413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_11467628413
  · decide +kernel

theorem prime_527510907433 : Nat.Prime 527510907433 := by
  apply nodeValid_prime [2, 3, 607, 1823, 2207] ⟨527510907433, 5, [(2, 3), (3, 3), (607, 1), (1823, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_607
    · exact prime_1823
    · exact prime_2207
  · decide +kernel

theorem prime_527510939273 : Nat.Prime 527510939273 := by
  apply nodeValid_prime [2, 31, 2127060239] ⟨527510939273, 3, [(2, 3), (31, 1), (2127060239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2127060239
  · decide +kernel

theorem prime_528356257489 : Nat.Prime 528356257489 := by
  apply nodeValid_prime [2, 3, 3669140677] ⟨528356257489, 13, [(2, 4), (3, 2), (3669140677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3669140677
  · decide +kernel

theorem prime_528356264057 : Nat.Prime 528356264057 := by
  apply nodeValid_prime [2, 19, 12497, 278149] ⟨528356264057, 3, [(2, 3), (19, 1), (12497, 1), (278149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_12497
    · exact prime_278149
  · decide +kernel

theorem prime_528356265341 : Nat.Prime 528356265341 := by
  apply nodeValid_prime [2, 5, 71, 3407, 109211] ⟨528356265341, 2, [(2, 2), (5, 1), (71, 1), (3407, 1), (109211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_3407
    · exact prime_109211
  · decide +kernel

theorem prime_529202477039 : Nat.Prime 529202477039 := by
  apply nodeValid_prime [2, 264601238519] ⟨529202477039, 11, [(2, 1), (264601238519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_264601238519
  · decide +kernel

theorem prime_529202477341 : Nat.Prime 529202477341 := by
  apply nodeValid_prime [2, 3, 5, 8353, 351971] ⟨529202477341, 2, [(2, 2), (3, 2), (5, 1), (8353, 1), (351971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8353
    · exact prime_351971
  · decide +kernel

theorem prime_529202495009 : Nat.Prime 529202495009 := by
  apply nodeValid_prime [2, 11, 53, 28366343] ⟨529202495009, 3, [(2, 5), (11, 1), (53, 1), (28366343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_28366343
  · decide +kernel

end Sude.Lucas.Generated
