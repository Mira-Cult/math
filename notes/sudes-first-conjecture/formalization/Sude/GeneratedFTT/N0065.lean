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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0061

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5101 : Nat.Prime 5101 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨5101, 6, [(2, 2), (3, 1), (5, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_5807 : Nat.Prime 5807 := by
  apply nodeValid_prime [2, 2903] ⟨5807, 5, [(2, 1), (2903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2903
  · decide +kernel

theorem prime_5897 : Nat.Prime 5897 := by
  apply nodeValid_prime [2, 11, 67] ⟨5897, 3, [(2, 3), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_8647 : Nat.Prime 8647 := by
  apply nodeValid_prime [2, 3, 11, 131] ⟨8647, 3, [(2, 1), (3, 1), (11, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
  · decide +kernel

theorem prime_8737 : Nat.Prime 8737 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨8737, 5, [(2, 5), (3, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_11579 : Nat.Prime 11579 := by
  apply nodeValid_prime [2, 7, 827] ⟨11579, 2, [(2, 1), (7, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_827
  · decide +kernel

theorem prime_12809 : Nat.Prime 12809 := by
  apply nodeValid_prime [2, 1601] ⟨12809, 3, [(2, 3), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1601
  · decide +kernel

theorem prime_13009 : Nat.Prime 13009 := by
  apply nodeValid_prime [2, 3, 271] ⟨13009, 7, [(2, 4), (3, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
  · decide +kernel

theorem prime_16567 : Nat.Prime 16567 := by
  apply nodeValid_prime [2, 3, 11, 251] ⟨16567, 3, [(2, 1), (3, 1), (11, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_251
  · decide +kernel

theorem prime_18149 : Nat.Prime 18149 := by
  apply nodeValid_prime [2, 13, 349] ⟨18149, 2, [(2, 2), (13, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_349
  · decide +kernel

theorem prime_22741 : Nat.Prime 22741 := by
  apply nodeValid_prime [2, 3, 5, 379] ⟨22741, 7, [(2, 2), (3, 1), (5, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_379
  · decide +kernel

theorem prime_23071 : Nat.Prime 23071 := by
  apply nodeValid_prime [2, 3, 5, 769] ⟨23071, 3, [(2, 1), (3, 1), (5, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_769
  · decide +kernel

theorem prime_24371 : Nat.Prime 24371 := by
  apply nodeValid_prime [2, 5, 2437] ⟨24371, 2, [(2, 1), (5, 1), (2437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2437
  · decide +kernel

theorem prime_28403 : Nat.Prime 28403 := by
  apply nodeValid_prime [2, 11, 1291] ⟨28403, 5, [(2, 1), (11, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1291
  · decide +kernel

theorem prime_30161 : Nat.Prime 30161 := by
  apply nodeValid_prime [2, 5, 13, 29] ⟨30161, 3, [(2, 4), (5, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_31319 : Nat.Prime 31319 := by
  apply nodeValid_prime [2, 7, 2237] ⟨31319, 7, [(2, 1), (7, 1), (2237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2237
  · decide +kernel

theorem prime_31397 : Nat.Prime 31397 := by
  apply nodeValid_prime [2, 47, 167] ⟨31397, 2, [(2, 2), (47, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_167
  · decide +kernel

theorem prime_31573 : Nat.Prime 31573 := by
  apply nodeValid_prime [2, 3, 877] ⟨31573, 5, [(2, 2), (3, 2), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_877
  · decide +kernel

theorem prime_33617 : Nat.Prime 33617 := by
  apply nodeValid_prime [2, 11, 191] ⟨33617, 3, [(2, 4), (11, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_191
  · decide +kernel

theorem prime_34949 : Nat.Prime 34949 := by
  apply nodeValid_prime [2, 8737] ⟨34949, 2, [(2, 2), (8737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8737
  · decide +kernel

theorem prime_37159 : Nat.Prime 37159 := by
  apply nodeValid_prime [2, 3, 11, 563] ⟨37159, 3, [(2, 1), (3, 1), (11, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_563
  · decide +kernel

theorem prime_50497 : Nat.Prime 50497 := by
  apply nodeValid_prime [2, 3, 263] ⟨50497, 5, [(2, 6), (3, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
  · decide +kernel

theorem prime_53401 : Nat.Prime 53401 := by
  apply nodeValid_prime [2, 3, 5, 89] ⟨53401, 7, [(2, 3), (3, 1), (5, 2), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_56543 : Nat.Prime 56543 := by
  apply nodeValid_prime [2, 17, 1663] ⟨56543, 5, [(2, 1), (17, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1663
  · decide +kernel

theorem prime_56807 : Nat.Prime 56807 := by
  apply nodeValid_prime [2, 28403] ⟨56807, 5, [(2, 1), (28403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28403
  · decide +kernel

theorem prime_60539 : Nat.Prime 60539 := by
  apply nodeValid_prime [2, 30269] ⟨60539, 2, [(2, 1), (30269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30269
  · decide +kernel

theorem prime_60889 : Nat.Prime 60889 := by
  apply nodeValid_prime [2, 3, 43, 59] ⟨60889, 21, [(2, 3), (3, 1), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_67271 : Nat.Prime 67271 := by
  apply nodeValid_prime [2, 5, 7, 31] ⟨67271, 14, [(2, 1), (5, 1), (7, 1), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_69557 : Nat.Prime 69557 := by
  apply nodeValid_prime [2, 17389] ⟨69557, 2, [(2, 2), (17389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17389
  · decide +kernel

theorem prime_69899 : Nat.Prime 69899 := by
  apply nodeValid_prime [2, 34949] ⟨69899, 2, [(2, 1), (34949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34949
  · decide +kernel

theorem prime_75041 : Nat.Prime 75041 := by
  apply nodeValid_prime [2, 5, 7, 67] ⟨75041, 3, [(2, 5), (5, 1), (7, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_79657 : Nat.Prime 79657 := by
  apply nodeValid_prime [2, 3, 3319] ⟨79657, 5, [(2, 3), (3, 1), (3319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3319
  · decide +kernel

theorem prime_80651 : Nat.Prime 80651 := by
  apply nodeValid_prime [2, 5, 1613] ⟨80651, 2, [(2, 1), (5, 2), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1613
  · decide +kernel

theorem prime_82349 : Nat.Prime 82349 := by
  apply nodeValid_prime [2, 7, 17, 173] ⟨82349, 3, [(2, 2), (7, 1), (17, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_173
  · decide +kernel

theorem prime_116731 : Nat.Prime 116731 := by
  apply nodeValid_prime [2, 3, 5, 1297] ⟨116731, 3, [(2, 1), (3, 2), (5, 1), (1297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1297
  · decide +kernel

theorem prime_122053 : Nat.Prime 122053 := by
  apply nodeValid_prime [2, 3, 7, 1453] ⟨122053, 2, [(2, 2), (3, 1), (7, 1), (1453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1453
  · decide +kernel

theorem prime_135271 : Nat.Prime 135271 := by
  apply nodeValid_prime [2, 3, 5, 167] ⟨135271, 11, [(2, 1), (3, 4), (5, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
  · decide +kernel

theorem prime_149729 : Nat.Prime 149729 := by
  apply nodeValid_prime [2, 4679] ⟨149729, 3, [(2, 5), (4679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4679
  · decide +kernel

theorem prime_156109 : Nat.Prime 156109 := by
  apply nodeValid_prime [2, 3, 13009] ⟨156109, 2, [(2, 2), (3, 1), (13009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13009
  · decide +kernel

theorem prime_161303 : Nat.Prime 161303 := by
  apply nodeValid_prime [2, 80651] ⟨161303, 5, [(2, 1), (80651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_80651
  · decide +kernel

theorem prime_167173 : Nat.Prime 167173 := by
  apply nodeValid_prime [2, 3, 13931] ⟨167173, 5, [(2, 2), (3, 1), (13931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13931
  · decide +kernel

theorem prime_179327 : Nat.Prime 179327 := by
  apply nodeValid_prime [2, 7, 12809] ⟨179327, 5, [(2, 1), (7, 1), (12809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12809
  · decide +kernel

theorem prime_211039 : Nat.Prime 211039 := by
  apply nodeValid_prime [2, 3, 17, 2069] ⟨211039, 3, [(2, 1), (3, 1), (17, 1), (2069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2069
  · decide +kernel

theorem prime_227603 : Nat.Prime 227603 := by
  apply nodeValid_prime [2, 31, 3671] ⟨227603, 2, [(2, 1), (31, 1), (3671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_3671
  · decide +kernel

theorem prime_248057 : Nat.Prime 248057 := by
  apply nodeValid_prime [2, 101, 307] ⟨248057, 3, [(2, 3), (101, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_307
  · decide +kernel

theorem prime_251177 : Nat.Prime 251177 := by
  apply nodeValid_prime [2, 31397] ⟨251177, 3, [(2, 3), (31397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31397
  · decide +kernel

theorem prime_279817 : Nat.Prime 279817 := by
  apply nodeValid_prime [2, 3, 89, 131] ⟨279817, 5, [(2, 3), (3, 1), (89, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_131
  · decide +kernel

theorem prime_310831 : Nat.Prime 310831 := by
  apply nodeValid_prime [2, 3, 5, 13, 797] ⟨310831, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_797
  · decide +kernel

theorem prime_313249 : Nat.Prime 313249 := by
  apply nodeValid_prime [2, 3, 13, 251] ⟨313249, 7, [(2, 5), (3, 1), (13, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_251
  · decide +kernel

theorem prime_321647 : Nat.Prime 321647 := by
  apply nodeValid_prime [2, 13, 89, 139] ⟨321647, 5, [(2, 1), (13, 1), (89, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_89
    · exact prime_139
  · decide +kernel

theorem prime_322607 : Nat.Prime 322607 := by
  apply nodeValid_prime [2, 161303] ⟨322607, 5, [(2, 1), (161303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_161303
  · decide +kernel

theorem prime_417457 : Nat.Prime 417457 := by
  apply nodeValid_prime [2, 3, 13, 223] ⟨417457, 10, [(2, 4), (3, 2), (13, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_223
  · decide +kernel

theorem prime_457117 : Nat.Prime 457117 := by
  apply nodeValid_prime [2, 3, 11, 3463] ⟨457117, 2, [(2, 2), (3, 1), (11, 1), (3463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3463
  · decide +kernel

theorem prime_486797 : Nat.Prime 486797 := by
  apply nodeValid_prime [2, 131, 929] ⟨486797, 2, [(2, 2), (131, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_929
  · decide +kernel

theorem prime_563743 : Nat.Prime 563743 := by
  apply nodeValid_prime [2, 3, 31319] ⟨563743, 3, [(2, 1), (3, 2), (31319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31319
  · decide +kernel

theorem prime_583301 : Nat.Prime 583301 := by
  apply nodeValid_prime [2, 5, 19, 307] ⟨583301, 2, [(2, 2), (5, 2), (19, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_307
  · decide +kernel

theorem prime_586841 : Nat.Prime 586841 := by
  apply nodeValid_prime [2, 5, 17, 863] ⟨586841, 6, [(2, 3), (5, 1), (17, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_863
  · decide +kernel

theorem prime_635287 : Nat.Prime 635287 := by
  apply nodeValid_prime [2, 3, 113, 937] ⟨635287, 5, [(2, 1), (3, 1), (113, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_937
  · decide +kernel

theorem prime_638171 : Nat.Prime 638171 := by
  apply nodeValid_prime [2, 5, 13, 4909] ⟨638171, 2, [(2, 1), (5, 1), (13, 1), (4909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4909
  · decide +kernel

theorem prime_679433 : Nat.Prime 679433 := by
  apply nodeValid_prime [2, 13, 47, 139] ⟨679433, 3, [(2, 3), (13, 1), (47, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_139
  · decide +kernel

theorem prime_700387 : Nat.Prime 700387 := by
  apply nodeValid_prime [2, 3, 116731] ⟨700387, 3, [(2, 1), (3, 1), (116731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_116731
  · decide +kernel

theorem prime_702431 : Nat.Prime 702431 := by
  apply nodeValid_prime [2, 5, 19, 3697] ⟨702431, 11, [(2, 1), (5, 1), (19, 1), (3697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3697
  · decide +kernel

theorem prime_811627 : Nat.Prime 811627 := by
  apply nodeValid_prime [2, 3, 135271] ⟨811627, 2, [(2, 1), (3, 1), (135271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_135271
  · decide +kernel

theorem prime_883933 : Nat.Prime 883933 := by
  apply nodeValid_prime [2, 3, 7, 17, 619] ⟨883933, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_619
  · decide +kernel

theorem prime_1111361 : Nat.Prime 1111361 := by
  apply nodeValid_prime [2, 5, 23, 151] ⟨1111361, 3, [(2, 6), (5, 1), (23, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_151
  · decide +kernel

theorem prime_1166603 : Nat.Prime 1166603 := by
  apply nodeValid_prime [2, 583301] ⟨1166603, 2, [(2, 1), (583301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_583301
  · decide +kernel

theorem prime_1252997 : Nat.Prime 1252997 := by
  apply nodeValid_prime [2, 313249] ⟨1252997, 2, [(2, 2), (313249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_313249
  · decide +kernel

theorem prime_1343233 : Nat.Prime 1343233 := by
  apply nodeValid_prime [2, 3, 11, 53] ⟨1343233, 10, [(2, 8), (3, 2), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_1491031 : Nat.Prime 1491031 := by
  apply nodeValid_prime [2, 3, 5, 16567] ⟨1491031, 15, [(2, 1), (3, 2), (5, 1), (16567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16567
  · decide +kernel

theorem prime_1679501 : Nat.Prime 1679501 := by
  apply nodeValid_prime [2, 5, 3359] ⟨1679501, 7, [(2, 2), (5, 3), (3359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3359
  · decide +kernel

theorem prime_2136019 : Nat.Prime 2136019 := by
  apply nodeValid_prime [2, 3, 19, 41, 457] ⟨2136019, 7, [(2, 1), (3, 1), (19, 1), (41, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_457
  · decide +kernel

theorem prime_2333207 : Nat.Prime 2333207 := by
  apply nodeValid_prime [2, 1166603] ⟨2333207, 5, [(2, 1), (1166603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1166603
  · decide +kernel

theorem prime_3505889 : Nat.Prime 3505889 := by
  apply nodeValid_prime [2, 89, 1231] ⟨3505889, 3, [(2, 5), (89, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1231
  · decide +kernel

theorem prime_3670237 : Nat.Prime 3670237 := by
  apply nodeValid_prime [2, 3, 269, 379] ⟨3670237, 2, [(2, 2), (3, 2), (269, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_379
  · decide +kernel

theorem prime_3970357 : Nat.Prime 3970357 := by
  apply nodeValid_prime [2, 3, 13, 31, 821] ⟨3970357, 2, [(2, 2), (3, 1), (13, 1), (31, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_821
  · decide +kernel

theorem prime_4136221 : Nat.Prime 4136221 := by
  apply nodeValid_prime [2, 3, 5, 11, 2089] ⟨4136221, 2, [(2, 2), (3, 2), (5, 1), (11, 1), (2089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2089
  · decide +kernel

theorem prime_4399163 : Nat.Prime 4399163 := by
  apply nodeValid_prime [2, 373, 5897] ⟨4399163, 2, [(2, 1), (373, 1), (5897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_5897
  · decide +kernel

theorem prime_4501621 : Nat.Prime 4501621 := by
  apply nodeValid_prime [2, 3, 5, 89, 281] ⟨4501621, 6, [(2, 2), (3, 2), (5, 1), (89, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_281
  · decide +kernel

theorem prime_4574891 : Nat.Prime 4574891 := by
  apply nodeValid_prime [2, 5, 79, 5791] ⟨4574891, 2, [(2, 1), (5, 1), (79, 1), (5791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_5791
  · decide +kernel

theorem prime_4683271 : Nat.Prime 4683271 := by
  apply nodeValid_prime [2, 3, 5, 156109] ⟨4683271, 6, [(2, 1), (3, 1), (5, 1), (156109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_156109
  · decide +kernel

theorem prime_7742569 : Nat.Prime 7742569 := by
  apply nodeValid_prime [2, 3, 322607] ⟨7742569, 11, [(2, 3), (3, 1), (322607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_322607
  · decide +kernel

theorem prime_7903349 : Nat.Prime 7903349 := by
  apply nodeValid_prime [2, 37, 53401] ⟨7903349, 2, [(2, 2), (37, 1), (53401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_53401
  · decide +kernel

theorem prime_8059399 : Nat.Prime 8059399 := by
  apply nodeValid_prime [2, 3, 1343233] ⟨8059399, 3, [(2, 1), (3, 1), (1343233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1343233
  · decide +kernel

theorem prime_8228183 : Nat.Prime 8228183 := by
  apply nodeValid_prime [2, 1429, 2879] ⟨8228183, 5, [(2, 1), (1429, 1), (2879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1429
    · exact prime_2879
  · decide +kernel

theorem prime_10671613 : Nat.Prime 10671613 := by
  apply nodeValid_prime [2, 3, 7, 18149] ⟨10671613, 5, [(2, 2), (3, 1), (7, 2), (18149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_18149
  · decide +kernel

theorem prime_12191239 : Nat.Prime 12191239 := by
  apply nodeValid_prime [2, 3, 127, 5333] ⟨12191239, 3, [(2, 1), (3, 2), (127, 1), (5333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_5333
  · decide +kernel

theorem prime_12908453 : Nat.Prime 12908453 := by
  apply nodeValid_prime [2, 1453, 2221] ⟨12908453, 2, [(2, 2), (1453, 1), (2221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1453
    · exact prime_2221
  · decide +kernel

theorem prime_13336333 : Nat.Prime 13336333 := by
  apply nodeValid_prime [2, 3, 1111361] ⟨13336333, 11, [(2, 2), (3, 1), (1111361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1111361
  · decide +kernel

theorem prime_14988569 : Nat.Prime 14988569 := by
  apply nodeValid_prime [2, 7, 19, 14087] ⟨14988569, 3, [(2, 3), (7, 1), (19, 1), (14087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_14087
  · decide +kernel

theorem prime_15257867 : Nat.Prime 15257867 := by
  apply nodeValid_prime [2, 13, 586841] ⟨15257867, 5, [(2, 1), (13, 1), (586841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_586841
  · decide +kernel

theorem prime_16384723 : Nat.Prime 16384723 := by
  apply nodeValid_prime [2, 3, 61, 89, 503] ⟨16384723, 3, [(2, 1), (3, 1), (61, 1), (89, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_89
    · exact prime_503
  · decide +kernel

theorem prime_21808489 : Nat.Prime 21808489 := by
  apply nodeValid_prime [2, 3, 13, 69899] ⟨21808489, 7, [(2, 3), (3, 1), (13, 1), (69899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_69899
  · decide +kernel

theorem prime_31293799 : Nat.Prime 31293799 := by
  apply nodeValid_prime [2, 3, 19, 277, 991] ⟨31293799, 3, [(2, 1), (3, 1), (19, 1), (277, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_277
    · exact prime_991
  · decide +kernel

theorem prime_35001751 : Nat.Prime 35001751 := by
  apply nodeValid_prime [2, 3, 5, 7, 59, 113] ⟨35001751, 12, [(2, 1), (3, 1), (5, 3), (7, 1), (59, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_113
  · decide +kernel

theorem prime_35004269 : Nat.Prime 35004269 := by
  apply nodeValid_prime [2, 13, 79, 8521] ⟨35004269, 2, [(2, 2), (13, 1), (79, 1), (8521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_8521
  · decide +kernel

theorem prime_39118483 : Nat.Prime 39118483 := by
  apply nodeValid_prime [2, 3, 13, 167173] ⟨39118483, 2, [(2, 1), (3, 2), (13, 1), (167173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_167173
  · decide +kernel

theorem prime_44586251 : Nat.Prime 44586251 := by
  apply nodeValid_prime [2, 5, 53, 673] ⟨44586251, 2, [(2, 1), (5, 4), (53, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_673
  · decide +kernel

theorem prime_45948313 : Nat.Prime 45948313 := by
  apply nodeValid_prime [2, 3, 638171] ⟨45948313, 5, [(2, 3), (3, 2), (638171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_638171
  · decide +kernel

theorem prime_48796151 : Nat.Prime 48796151 := by
  apply nodeValid_prime [2, 5, 13, 41, 1831] ⟨48796151, 17, [(2, 1), (5, 2), (13, 1), (41, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_1831
  · decide +kernel

theorem prime_55905257 : Nat.Prime 55905257 := by
  apply nodeValid_prime [2, 11, 635287] ⟨55905257, 3, [(2, 3), (11, 1), (635287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_635287
  · decide +kernel

theorem prime_57366223 : Nat.Prime 57366223 := by
  apply nodeValid_prime [2, 3, 317, 30161] ⟨57366223, 6, [(2, 1), (3, 1), (317, 1), (30161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
    · exact prime_30161
  · decide +kernel

theorem prime_57572891 : Nat.Prime 57572891 := by
  apply nodeValid_prime [2, 5, 31, 229, 811] ⟨57572891, 10, [(2, 1), (5, 1), (31, 1), (229, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_229
    · exact prime_811
  · decide +kernel

theorem prime_63106003 : Nat.Prime 63106003 := by
  apply nodeValid_prime [2, 3, 3505889] ⟨63106003, 2, [(2, 1), (3, 2), (3505889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3505889
  · decide +kernel

theorem prime_77450719 : Nat.Prime 77450719 := by
  apply nodeValid_prime [2, 3, 12908453] ⟨77450719, 3, [(2, 1), (3, 1), (12908453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12908453
  · decide +kernel

theorem prime_97597081 : Nat.Prime 97597081 := by
  apply nodeValid_prime [2, 3, 5, 7, 38729] ⟨97597081, 11, [(2, 3), (3, 2), (5, 1), (7, 1), (38729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_38729
  · decide +kernel

theorem prime_98308339 : Nat.Prime 98308339 := by
  apply nodeValid_prime [2, 3, 16384723] ⟨98308339, 29, [(2, 1), (3, 1), (16384723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16384723
  · decide +kernel

theorem prime_115145783 : Nat.Prime 115145783 := by
  apply nodeValid_prime [2, 57572891] ⟨115145783, 5, [(2, 1), (57572891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57572891
  · decide +kernel

theorem prime_130108499 : Nat.Prime 130108499 := by
  apply nodeValid_prime [2, 13, 41, 122053] ⟨130108499, 2, [(2, 1), (13, 1), (41, 1), (122053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_122053
  · decide +kernel

theorem prime_154676521 : Nat.Prime 154676521 := by
  apply nodeValid_prime [2, 3, 5, 197, 727] ⟨154676521, 14, [(2, 3), (3, 3), (5, 1), (197, 1), (727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
    · exact prime_727
  · decide +kernel

theorem prime_187089667 : Nat.Prime 187089667 := by
  apply nodeValid_prime [2, 3, 137, 227603] ⟨187089667, 2, [(2, 1), (3, 1), (137, 1), (227603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_227603
  · decide +kernel

theorem prime_276697747 : Nat.Prime 276697747 := by
  apply nodeValid_prime [2, 3, 13, 17, 69557] ⟨276697747, 2, [(2, 1), (3, 2), (13, 1), (17, 1), (69557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_69557
  · decide +kernel

theorem prime_335981809 : Nat.Prime 335981809 := by
  apply nodeValid_prime [2, 3, 2333207] ⟨335981809, 39, [(2, 4), (3, 2), (2333207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2333207
  · decide +kernel

theorem prime_351712307 : Nat.Prime 351712307 := by
  apply nodeValid_prime [2, 11, 19, 37, 22741] ⟨351712307, 2, [(2, 1), (11, 1), (19, 1), (37, 1), (22741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_37
    · exact prime_22741
  · decide +kernel

theorem prime_395058701 : Nat.Prime 395058701 := by
  apply nodeValid_prime [2, 5, 1249, 3163] ⟨395058701, 2, [(2, 2), (5, 2), (1249, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1249
    · exact prime_3163
  · decide +kernel

theorem prime_463370477 : Nat.Prime 463370477 := by
  apply nodeValid_prime [2, 467, 248057] ⟨463370477, 2, [(2, 2), (467, 1), (248057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_467
    · exact prime_248057
  · decide +kernel

theorem prime_619841137 : Nat.Prime 619841137 := by
  apply nodeValid_prime [2, 3, 409, 31573] ⟨619841137, 5, [(2, 4), (3, 1), (409, 1), (31573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_409
    · exact prime_31573
  · decide +kernel

theorem prime_636861061 : Nat.Prime 636861061 := by
  apply nodeValid_prime [2, 3, 5, 11, 321647] ⟨636861061, 2, [(2, 2), (3, 2), (5, 1), (11, 1), (321647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_321647
  · decide +kernel

theorem prime_780755837 : Nat.Prime 780755837 := by
  apply nodeValid_prime [2, 7, 61, 457117] ⟨780755837, 3, [(2, 2), (7, 1), (61, 1), (457117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_457117
  · decide +kernel

theorem prime_950149513 : Nat.Prime 950149513 := by
  apply nodeValid_prime [2, 3, 13, 67, 109, 139] ⟨950149513, 5, [(2, 3), (3, 2), (13, 1), (67, 1), (109, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
    · exact prime_109
    · exact prime_139
  · decide +kernel

theorem prime_1146445019 : Nat.Prime 1146445019 := by
  apply nodeValid_prime [2, 337, 977, 1741] ⟨1146445019, 2, [(2, 1), (337, 1), (977, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_977
    · exact prime_1741
  · decide +kernel

theorem prime_1463884531 : Nat.Prime 1463884531 := by
  apply nodeValid_prime [2, 3, 5, 48796151] ⟨1463884531, 2, [(2, 1), (3, 1), (5, 1), (48796151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_48796151
  · decide +kernel

theorem prime_1663041851 : Nat.Prime 1663041851 := by
  apply nodeValid_prime [2, 5, 59, 563743] ⟨1663041851, 6, [(2, 1), (5, 2), (59, 1), (563743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_563743
  · decide +kernel

theorem prime_1979993471 : Nat.Prime 1979993471 := by
  apply nodeValid_prime [2, 5, 7, 13, 310831] ⟨1979993471, 7, [(2, 1), (5, 1), (7, 2), (13, 1), (310831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_310831
  · decide +kernel

theorem prime_2813698457 : Nat.Prime 2813698457 := by
  apply nodeValid_prime [2, 351712307] ⟨2813698457, 3, [(2, 3), (351712307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_351712307
  · decide +kernel

theorem prime_2893644569 : Nat.Prime 2893644569 := by
  apply nodeValid_prime [2, 6397, 56543] ⟨2893644569, 3, [(2, 3), (6397, 1), (56543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6397
    · exact prime_56543
  · decide +kernel

theorem prime_2967283967 : Nat.Prime 2967283967 := by
  apply nodeValid_prime [2, 311, 1187, 4019] ⟨2967283967, 5, [(2, 1), (311, 1), (1187, 1), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_1187
    · exact prime_4019
  · decide +kernel

theorem prime_2993434673 : Nat.Prime 2993434673 := by
  apply nodeValid_prime [2, 187089667] ⟨2993434673, 3, [(2, 4), (187089667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_187089667
  · decide +kernel

theorem prime_3504905489 : Nat.Prime 3504905489 := by
  apply nodeValid_prime [2, 7, 31293799] ⟨3504905489, 3, [(2, 4), (7, 1), (31293799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31293799
  · decide +kernel

theorem prime_3536676677 : Nat.Prime 3536676677 := by
  apply nodeValid_prime [2, 13, 1117, 60889] ⟨3536676677, 2, [(2, 2), (13, 1), (1117, 1), (60889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1117
    · exact prime_60889
  · decide +kernel

theorem prime_11423381507 : Nat.Prime 11423381507 := by
  apply nodeValid_prime [2, 17, 335981809] ⟨11423381507, 2, [(2, 1), (17, 1), (335981809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_335981809
  · decide +kernel

theorem prime_13304334809 : Nat.Prime 13304334809 := by
  apply nodeValid_prime [2, 1663041851] ⟨13304334809, 3, [(2, 3), (1663041851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1663041851
  · decide +kernel

theorem prime_22070190869 : Nat.Prime 22070190869 := by
  apply nodeValid_prime [2, 11, 23, 21808489] ⟨22070190869, 2, [(2, 2), (11, 1), (23, 1), (21808489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_21808489
  · decide +kernel

theorem prime_31754596061 : Nat.Prime 31754596061 := by
  apply nodeValid_prime [2, 5, 11, 233, 683, 907] ⟨31754596061, 2, [(2, 2), (5, 1), (11, 1), (233, 1), (683, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_233
    · exact prime_683
    · exact prime_907
  · decide +kernel

theorem prime_40988766869 : Nat.Prime 40988766869 := by
  apply nodeValid_prime [2, 7, 1463884531] ⟨40988766869, 2, [(2, 2), (7, 1), (1463884531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1463884531
  · decide +kernel

theorem prime_73567314151 : Nat.Prime 73567314151 := by
  apply nodeValid_prime [2, 3, 5, 11, 44586251] ⟨73567314151, 6, [(2, 1), (3, 1), (5, 2), (11, 1), (44586251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_44586251
  · decide +kernel

theorem prime_130070740951 : Nat.Prime 130070740951 := by
  apply nodeValid_prime [2, 3, 5, 109, 883933] ⟨130070740951, 3, [(2, 1), (3, 3), (5, 2), (109, 1), (883933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_883933
  · decide +kernel

theorem prime_165526456889 : Nat.Prime 165526456889 := by
  apply nodeValid_prime [2, 13, 37, 53, 811627] ⟨165526456889, 3, [(2, 3), (13, 1), (37, 1), (53, 1), (811627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_53
    · exact prime_811627
  · decide +kernel

theorem prime_217824553603 : Nat.Prime 217824553603 := by
  apply nodeValid_prime [2, 3, 241, 5807, 8647] ⟨217824553603, 2, [(2, 1), (3, 2), (241, 1), (5807, 1), (8647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_5807
    · exact prime_8647
  · decide +kernel

theorem prime_331841726149 : Nat.Prime 331841726149 := by
  apply nodeValid_prime [2, 3, 56807, 486797] ⟨331841726149, 2, [(2, 2), (3, 1), (56807, 1), (486797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_56807
    · exact prime_486797
  · decide +kernel

theorem prime_1299150596987 : Nat.Prime 1299150596987 := by
  apply nodeValid_prime [2, 11, 211039, 279817] ⟨1299150596987, 2, [(2, 1), (11, 1), (211039, 1), (279817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_211039
    · exact prime_279817
  · decide +kernel

theorem prime_1299150647849 : Nat.Prime 1299150647849 := by
  apply nodeValid_prime [2, 17, 23, 593, 700387] ⟨1299150647849, 3, [(2, 3), (17, 1), (23, 1), (593, 1), (700387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_593
    · exact prime_700387
  · decide +kernel

theorem prime_1299150648083 : Nat.Prime 1299150648083 := by
  apply nodeValid_prime [2, 7, 31, 2993434673] ⟨1299150648083, 5, [(2, 1), (7, 1), (31, 1), (2993434673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_2993434673
  · decide +kernel

theorem prime_1300707374887 : Nat.Prime 1300707374887 := by
  apply nodeValid_prime [2, 3, 311, 77450719] ⟨1300707374887, 3, [(2, 1), (3, 3), (311, 1), (77450719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_77450719
  · decide +kernel

theorem prime_1300707374983 : Nat.Prime 1300707374983 := by
  apply nodeValid_prime [2, 3, 48157, 4501621] ⟨1300707374983, 6, [(2, 1), (3, 1), (48157, 1), (4501621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_48157
    · exact prime_4501621
  · decide +kernel

theorem prime_1300707409511 : Nat.Prime 1300707409511 := by
  apply nodeValid_prime [2, 5, 130070740951] ⟨1300707409511, 11, [(2, 1), (5, 1), (130070740951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_130070740951
  · decide +kernel

theorem prime_1302265460497 : Nat.Prime 1302265460497 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 379, 5501] ⟨1302265460497, 20, [(2, 4), (3, 1), (7, 1), (11, 1), (13, 2), (379, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_379
    · exact prime_5501
  · decide +kernel

theorem prime_1302265460641 : Nat.Prime 1302265460641 := by
  apply nodeValid_prime [2, 3, 5, 67, 97, 417457] ⟨1302265460641, 19, [(2, 5), (3, 1), (5, 1), (67, 1), (97, 1), (417457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_97
    · exact prime_417457
  · decide +kernel

theorem prime_1302265491799 : Nat.Prime 1302265491799 := by
  apply nodeValid_prime [2, 3, 19, 11423381507] ⟨1302265491799, 3, [(2, 1), (3, 1), (19, 1), (11423381507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11423381507
  · decide +kernel

theorem prime_1303824810661 : Nat.Prime 1303824810661 := by
  apply nodeValid_prime [2, 3, 5, 31, 11579, 60539] ⟨1303824810661, 6, [(2, 2), (3, 1), (5, 1), (31, 1), (11579, 1), (60539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_11579
    · exact prime_60539
  · decide +kernel

theorem prime_1303824811283 : Nat.Prime 1303824811283 := by
  apply nodeValid_prime [2, 7, 13304334809] ⟨1303824811283, 2, [(2, 1), (7, 2), (13304334809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13304334809
  · decide +kernel

theorem prime_1303824841909 : Nat.Prime 1303824841909 := by
  apply nodeValid_prime [2, 3, 31, 3504905489] ⟨1303824841909, 6, [(2, 2), (3, 1), (31, 1), (3504905489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3504905489
  · decide +kernel

theorem prime_1305385434247 : Nat.Prime 1305385434247 := by
  apply nodeValid_prime [2, 3, 281, 461, 1679501] ⟨1305385434247, 3, [(2, 1), (3, 1), (281, 1), (461, 1), (1679501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_461
    · exact prime_1679501
  · decide +kernel

theorem prime_1305385434523 : Nat.Prime 1305385434523 := by
  apply nodeValid_prime [2, 3, 13, 619841137] ⟨1305385434523, 3, [(2, 1), (3, 4), (13, 1), (619841137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_619841137
  · decide +kernel

theorem prime_1305385456099 : Nat.Prime 1305385456099 := by
  apply nodeValid_prime [2, 3, 53, 59, 277, 251177] ⟨1305385456099, 2, [(2, 1), (3, 1), (53, 1), (59, 1), (277, 1), (251177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_59
    · exact prime_277
    · exact prime_251177
  · decide +kernel

theorem prime_1306947321619 : Nat.Prime 1306947321619 := by
  apply nodeValid_prime [2, 3, 217824553603] ⟨1306947321619, 2, [(2, 1), (3, 1), (217824553603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_217824553603
  · decide +kernel

theorem prime_1306947321661 : Nat.Prime 1306947321661 := by
  apply nodeValid_prime [2, 3, 5, 19, 1146445019] ⟨1306947321661, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (1146445019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_1146445019
  · decide +kernel

theorem prime_1306947335671 : Nat.Prime 1306947335671 := by
  apply nodeValid_prime [2, 3, 5, 3301, 4399163] ⟨1306947335671, 15, [(2, 1), (3, 2), (5, 1), (3301, 1), (4399163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3301
    · exact prime_4399163
  · decide +kernel

theorem prime_1308510478969 : Nat.Prime 1308510478969 := by
  apply nodeValid_prime [2, 3, 7, 11, 4729, 149729] ⟨1308510478969, 13, [(2, 3), (3, 1), (7, 1), (11, 1), (4729, 1), (149729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_4729
    · exact prime_149729
  · decide +kernel

theorem prime_1308510499609 : Nat.Prime 1308510499609 := by
  apply nodeValid_prime [2, 3, 13, 131, 10671613] ⟨1308510499609, 7, [(2, 3), (3, 2), (13, 1), (131, 1), (10671613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_131
    · exact prime_10671613
  · decide +kernel

theorem prime_1308510502639 : Nat.Prime 1308510502639 := by
  apply nodeValid_prime [2, 3, 73, 4397, 679433] ⟨1308510502639, 7, [(2, 1), (3, 1), (73, 1), (4397, 1), (679433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_4397
    · exact prime_679433
  · decide +kernel

theorem prime_1310074877149 : Nat.Prime 1310074877149 := by
  apply nodeValid_prime [2, 3, 31, 887, 3970357] ⟨1310074877149, 2, [(2, 2), (3, 1), (31, 1), (887, 1), (3970357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_887
    · exact prime_3970357
  · decide +kernel

theorem prime_1310074936543 : Nat.Prime 1310074936543 := by
  apply nodeValid_prime [2, 3, 5303, 4574891] ⟨1310074936543, 3, [(2, 1), (3, 3), (5303, 1), (4574891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5303
    · exact prime_4574891
  · decide +kernel

theorem prime_1310074936939 : Nat.Prime 1310074936939 := by
  apply nodeValid_prime [2, 3, 9209, 7903349] ⟨1310074936939, 2, [(2, 1), (3, 2), (9209, 1), (7903349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9209
    · exact prime_7903349
  · decide +kernel

theorem prime_1311640539809 : Nat.Prime 1311640539809 := by
  apply nodeValid_prime [2, 40988766869] ⟨1311640539809, 3, [(2, 5), (40988766869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40988766869
  · decide +kernel

theorem prime_1311640540061 : Nat.Prime 1311640540061 := by
  apply nodeValid_prime [2, 5, 29, 33617, 67271] ⟨1311640540061, 13, [(2, 2), (5, 1), (29, 1), (33617, 1), (67271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_33617
    · exact prime_67271
  · decide +kernel

theorem prime_1311640542899 : Nat.Prime 1311640542899 := by
  apply nodeValid_prime [2, 7, 2039, 45948313] ⟨1311640542899, 2, [(2, 1), (7, 1), (2039, 1), (45948313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2039
    · exact prime_45948313
  · decide +kernel

theorem prime_1313207474311 : Nat.Prime 1313207474311 := by
  apply nodeValid_prime [2, 3, 5, 373, 39118483] ⟨1313207474311, 3, [(2, 1), (3, 2), (5, 1), (373, 1), (39118483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_373
    · exact prime_39118483
  · decide +kernel

theorem prime_1313207507263 : Nat.Prime 1313207507263 := by
  apply nodeValid_prime [2, 3, 7, 113, 276697747] ⟨1313207507263, 3, [(2, 1), (3, 1), (7, 1), (113, 1), (276697747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
    · exact prime_276697747
  · decide +kernel

theorem prime_1313207507783 : Nat.Prime 1313207507783 := by
  apply nodeValid_prime [2, 1031, 636861061] ⟨1313207507783, 5, [(2, 1), (1031, 1), (636861061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1031
    · exact prime_636861061
  · decide +kernel

theorem prime_1314775667423 : Nat.Prime 1314775667423 := by
  apply nodeValid_prime [2, 7, 19, 24181, 29201] ⟨1314775667423, 5, [(2, 1), (7, 2), (19, 1), (24181, 1), (29201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_24181
    · exact prime_29201
  · decide +kernel

theorem prime_1314775725139 : Nat.Prime 1314775725139 := by
  apply nodeValid_prime [2, 3, 5477, 13336333] ⟨1314775725139, 3, [(2, 1), (3, 2), (5477, 1), (13336333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5477
    · exact prime_13336333
  · decide +kernel

theorem prime_1314775725787 : Nat.Prime 1314775725787 := by
  apply nodeValid_prime [2, 3, 743, 98308339] ⟨1314775725787, 2, [(2, 1), (3, 2), (743, 1), (98308339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_743
    · exact prime_98308339
  · decide +kernel

theorem prime_1316345125967 : Nat.Prime 1316345125967 := by
  apply nodeValid_prime [2, 13, 503, 7742569] ⟨1316345125967, 5, [(2, 1), (13, 2), (503, 1), (7742569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_503
    · exact prime_7742569
  · decide +kernel

theorem prime_1316345180999 : Nat.Prime 1316345180999 := by
  apply nodeValid_prime [2, 179327, 3670237] ⟨1316345180999, 7, [(2, 1), (179327, 1), (3670237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179327
    · exact prime_3670237
  · decide +kernel

theorem prime_1316345181323 : Nat.Prime 1316345181323 := by
  apply nodeValid_prime [2, 61, 193, 55905257] ⟨1316345181323, 2, [(2, 1), (61, 1), (193, 1), (55905257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_193
    · exact prime_55905257
  · decide +kernel

theorem prime_1317915824789 : Nat.Prime 1317915824789 := by
  apply nodeValid_prime [2, 79657, 4136221] ⟨1317915824789, 2, [(2, 2), (79657, 1), (4136221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79657
    · exact prime_4136221
  · decide +kernel

theorem prime_1317915826537 : Nat.Prime 1317915826537 := by
  apply nodeValid_prime [2, 3, 139, 395058701] ⟨1317915826537, 5, [(2, 3), (3, 1), (139, 1), (395058701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_395058701
  · decide +kernel

theorem prime_1317915852857 : Nat.Prime 1317915852857 := by
  apply nodeValid_prime [2, 211, 780755837] ⟨1317915852857, 3, [(2, 3), (211, 1), (780755837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_780755837
  · decide +kernel

theorem prime_1319487849161 : Nat.Prime 1319487849161 := by
  apply nodeValid_prime [2, 5, 13, 23, 2969, 37159] ⟨1319487849161, 3, [(2, 3), (5, 1), (13, 1), (23, 1), (2969, 1), (37159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_23
    · exact prime_2969
    · exact prime_37159
  · decide +kernel

theorem prime_1319487882247 : Nat.Prime 1319487882247 := by
  apply nodeValid_prime [2, 3, 59, 151, 8228183] ⟨1319487882247, 3, [(2, 1), (3, 2), (59, 1), (151, 1), (8228183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_151
    · exact prime_8228183
  · decide +kernel

theorem prime_1319487883451 : Nat.Prime 1319487883451 := by
  apply nodeValid_prime [2, 5, 11, 1609, 1491031] ⟨1319487883451, 2, [(2, 1), (5, 2), (11, 1), (1609, 1), (1491031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1609
    · exact prime_1491031
  · decide +kernel

theorem prime_1321061066803 : Nat.Prime 1321061066803 := by
  apply nodeValid_prime [2, 3, 1163, 63106003] ⟨1321061066803, 5, [(2, 1), (3, 2), (1163, 1), (63106003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1163
    · exact prime_63106003
  · decide +kernel

theorem prime_1321061066869 : Nat.Prime 1321061066869 := by
  apply nodeValid_prime [2, 3, 29, 83, 1427, 32051] ⟨1321061066869, 10, [(2, 2), (3, 1), (29, 1), (83, 1), (1427, 1), (32051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_83
    · exact prime_1427
    · exact prime_32051
  · decide +kernel

theorem prime_1321061112061 : Nat.Prime 1321061112061 := by
  apply nodeValid_prime [2, 3, 5, 17, 37, 35004269] ⟨1321061112061, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (37, 1), (35004269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_37
    · exact prime_35004269
  · decide +kernel

theorem prime_1322635637489 : Nat.Prime 1322635637489 := by
  apply nodeValid_prime [2, 11, 131, 57366223] ⟨1322635637489, 3, [(2, 4), (11, 1), (131, 1), (57366223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_131
    · exact prime_57366223
  · decide +kernel

theorem prime_1322635638629 : Nat.Prime 1322635638629 := by
  apply nodeValid_prime [2, 167, 1979993471] ⟨1322635638629, 2, [(2, 2), (167, 1), (1979993471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_1979993471
  · decide +kernel

theorem prime_1322635641713 : Nat.Prime 1322635641713 := by
  apply nodeValid_prime [2, 7, 11, 97597081] ⟨1322635641713, 3, [(2, 4), (7, 1), (11, 2), (97597081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_97597081
  · decide +kernel

theorem prime_1324211452141 : Nat.Prime 1324211452141 := by
  apply nodeValid_prime [2, 3, 5, 22070190869] ⟨1324211452141, 6, [(2, 2), (3, 1), (5, 1), (22070190869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22070190869
  · decide +kernel

theorem prime_1324211654719 : Nat.Prime 1324211654719 := by
  apply nodeValid_prime [2, 3, 73567314151] ⟨1324211654719, 3, [(2, 1), (3, 2), (73567314151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73567314151
  · decide +kernel

theorem prime_1324211655113 : Nat.Prime 1324211655113 := by
  apply nodeValid_prime [2, 165526456889] ⟨1324211655113, 3, [(2, 3), (165526456889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_165526456889
  · decide +kernel

theorem prime_1325788534607 : Nat.Prime 1325788534607 := by
  apply nodeValid_prime [2, 569, 23071, 50497] ⟨1325788534607, 5, [(2, 1), (569, 1), (23071, 1), (50497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_569
    · exact prime_23071
    · exact prime_50497
  · decide +kernel

theorem prime_1325788544959 : Nat.Prime 1325788544959 := by
  apply nodeValid_prime [2, 3, 31, 47, 71, 2136019] ⟨1325788544959, 3, [(2, 1), (3, 1), (31, 1), (47, 1), (71, 1), (2136019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_47
    · exact prime_71
    · exact prime_2136019
  · decide +kernel

theorem prime_1325788545463 : Nat.Prime 1325788545463 := by
  apply nodeValid_prime [2, 3, 19, 101, 115145783] ⟨1325788545463, 3, [(2, 1), (3, 1), (19, 1), (101, 1), (115145783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_101
    · exact prime_115145783
  · decide +kernel

theorem prime_1327366896503 : Nat.Prime 1327366896503 := by
  apply nodeValid_prime [2, 82349, 8059399] ⟨1327366896503, 5, [(2, 1), (82349, 1), (8059399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_82349
    · exact prime_8059399
  · decide +kernel

theorem prime_1327366904597 : Nat.Prime 1327366904597 := by
  apply nodeValid_prime [2, 331841726149] ⟨1327366904597, 2, [(2, 2), (331841726149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_331841726149
  · decide +kernel

theorem prime_1327366906799 : Nat.Prime 1327366906799 := by
  apply nodeValid_prime [2, 5101, 130108499] ⟨1327366906799, 13, [(2, 1), (5101, 1), (130108499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5101
    · exact prime_130108499
  · decide +kernel

theorem prime_1328946481817 : Nat.Prime 1328946481817 := by
  apply nodeValid_prime [2, 11083, 14988569] ⟨1328946481817, 3, [(2, 3), (11083, 1), (14988569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11083
    · exact prime_14988569
  · decide +kernel

theorem prime_1328946481969 : Nat.Prime 1328946481969 := by
  apply nodeValid_prime [2, 3, 7, 113, 35001751] ⟨1328946481969, 11, [(2, 4), (3, 1), (7, 1), (113, 1), (35001751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
    · exact prime_35001751
  · decide +kernel

theorem prime_1328946528037 : Nat.Prime 1328946528037 := by
  apply nodeValid_prime [2, 3, 239, 463370477] ⟨1328946528037, 2, [(2, 2), (3, 1), (239, 1), (463370477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_239
    · exact prime_463370477
  · decide +kernel

theorem prime_1330527433643 : Nat.Prime 1330527433643 := by
  apply nodeValid_prime [2, 11, 17, 23, 154676521] ⟨1330527433643, 2, [(2, 1), (11, 1), (17, 1), (23, 1), (154676521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_23
    · exact prime_154676521
  · decide +kernel

theorem prime_1330527441983 : Nat.Prime 1330527441983 := by
  apply nodeValid_prime [2, 197, 277, 12191239] ⟨1330527441983, 5, [(2, 1), (197, 1), (277, 1), (12191239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_197
    · exact prime_277
    · exact prime_12191239
  · decide +kernel

theorem prime_1330527442373 : Nat.Prime 1330527442373 := by
  apply nodeValid_prime [2, 71, 3739, 1252997] ⟨1330527442373, 2, [(2, 2), (71, 1), (3739, 1), (1252997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_3739
    · exact prime_1252997
  · decide +kernel

theorem prime_1332109602997 : Nat.Prime 1332109602997 := by
  apply nodeValid_prime [2, 3, 31, 307, 1063, 10973] ⟨1332109602997, 2, [(2, 2), (3, 1), (31, 1), (307, 1), (1063, 1), (10973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_307
    · exact prime_1063
    · exact prime_10973
  · decide +kernel

theorem prime_1332109603241 : Nat.Prime 1332109603241 := by
  apply nodeValid_prime [2, 5, 13, 547, 4683271] ⟨1332109603241, 3, [(2, 3), (5, 1), (13, 1), (547, 1), (4683271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_547
    · exact prime_4683271
  · decide +kernel

theorem prime_1332109617227 : Nat.Prime 1332109617227 := by
  apply nodeValid_prime [2, 701, 950149513] ⟨1332109617227, 2, [(2, 1), (701, 1), (950149513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_701
    · exact prime_950149513
  · decide +kernel

theorem prime_1333693034563 : Nat.Prime 1333693034563 := by
  apply nodeValid_prime [2, 3, 7, 31754596061] ⟨1333693034563, 3, [(2, 1), (3, 1), (7, 1), (31754596061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31754596061
  · decide +kernel

theorem prime_1333693037179 : Nat.Prime 1333693037179 := by
  apply nodeValid_prime [2, 3, 31, 3539, 75041] ⟨1333693037179, 2, [(2, 1), (3, 4), (31, 1), (3539, 1), (75041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3539
    · exact prime_75041
  · decide +kernel

theorem prime_1333693068619 : Nat.Prime 1333693068619 := by
  apply nodeValid_prime [2, 3, 79, 2813698457] ⟨1333693068619, 2, [(2, 1), (3, 1), (79, 1), (2813698457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_2813698457
  · decide +kernel

theorem prime_1335277778867 : Nat.Prime 1335277778867 := by
  apply nodeValid_prime [2, 17, 37, 269, 1307, 3019] ⟨1335277778867, 2, [(2, 1), (17, 1), (37, 1), (269, 1), (1307, 1), (3019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_269
    · exact prime_1307
    · exact prime_3019
  · decide +kernel

theorem prime_1335277780279 : Nat.Prime 1335277780279 := by
  apply nodeValid_prime [2, 3, 13, 24371, 702431] ⟨1335277780279, 3, [(2, 1), (3, 1), (13, 1), (24371, 1), (702431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_24371
    · exact prime_702431
  · decide +kernel

theorem prime_1335277785151 : Nat.Prime 1335277785151 := by
  apply nodeValid_prime [2, 3, 5, 2967283967] ⟨1335277785151, 7, [(2, 1), (3, 2), (5, 2), (2967283967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2967283967
  · decide +kernel

theorem prime_1336863783907 : Nat.Prime 1336863783907 := by
  apply nodeValid_prime [2, 3, 7, 3536676677] ⟨1336863783907, 5, [(2, 1), (3, 3), (7, 1), (3536676677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3536676677
  · decide +kernel

theorem prime_1336863790807 : Nat.Prime 1336863790807 := by
  apply nodeValid_prime [2, 3, 17, 859, 15257867] ⟨1336863790807, 3, [(2, 1), (3, 1), (17, 1), (859, 1), (15257867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_859
    · exact prime_15257867
  · decide +kernel

theorem prime_1336863790879 : Nat.Prime 1336863790879 := by
  apply nodeValid_prime [2, 3, 7, 11, 2893644569] ⟨1336863790879, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (2893644569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_2893644569
  · decide +kernel

end Sude.Lucas.Generated
