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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0098
import Sude.GeneratedFTT.N0104
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0123

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_28697 : Nat.Prime 28697 := by
  apply nodeValid_prime [2, 17, 211] ⟨28697, 3, [(2, 3), (17, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_211
  · decide +kernel

theorem prime_29587 : Nat.Prime 29587 := by
  apply nodeValid_prime [2, 3, 4931] ⟨29587, 2, [(2, 1), (3, 1), (4931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4931
  · decide +kernel

theorem prime_36643 : Nat.Prime 36643 := by
  apply nodeValid_prime [2, 3, 31, 197] ⟨36643, 3, [(2, 1), (3, 1), (31, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_197
  · decide +kernel

theorem prime_39563 : Nat.Prime 39563 := by
  apply nodeValid_prime [2, 131, 151] ⟨39563, 2, [(2, 1), (131, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_151
  · decide +kernel

theorem prime_39679 : Nat.Prime 39679 := by
  apply nodeValid_prime [2, 3, 17, 389] ⟨39679, 6, [(2, 1), (3, 1), (17, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_389
  · decide +kernel

theorem prime_46769 : Nat.Prime 46769 := by
  apply nodeValid_prime [2, 37, 79] ⟨46769, 3, [(2, 4), (37, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_79
  · decide +kernel

theorem prime_51157 : Nat.Prime 51157 := by
  apply nodeValid_prime [2, 3, 7, 29] ⟨51157, 5, [(2, 2), (3, 2), (7, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_60259 : Nat.Prime 60259 := by
  apply nodeValid_prime [2, 3, 11, 83] ⟨60259, 3, [(2, 1), (3, 1), (11, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83
  · decide +kernel

theorem prime_61331 : Nat.Prime 61331 := by
  apply nodeValid_prime [2, 5, 6133] ⟨61331, 2, [(2, 1), (5, 1), (6133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6133
  · decide +kernel

theorem prime_78553 : Nat.Prime 78553 := by
  apply nodeValid_prime [2, 3, 1091] ⟨78553, 5, [(2, 3), (3, 2), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1091
  · decide +kernel

theorem prime_84247 : Nat.Prime 84247 := by
  apply nodeValid_prime [2, 3, 19, 739] ⟨84247, 5, [(2, 1), (3, 1), (19, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_739
  · decide +kernel

theorem prime_87149 : Nat.Prime 87149 := by
  apply nodeValid_prime [2, 21787] ⟨87149, 2, [(2, 2), (21787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21787
  · decide +kernel

theorem prime_103483 : Nat.Prime 103483 := by
  apply nodeValid_prime [2, 3, 5749] ⟨103483, 2, [(2, 1), (3, 2), (5749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5749
  · decide +kernel

theorem prime_112687 : Nat.Prime 112687 := by
  apply nodeValid_prime [2, 3, 7, 2683] ⟨112687, 5, [(2, 1), (3, 1), (7, 1), (2683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2683
  · decide +kernel

theorem prime_121687 : Nat.Prime 121687 := by
  apply nodeValid_prime [2, 3, 17, 1193] ⟨121687, 5, [(2, 1), (3, 1), (17, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1193
  · decide +kernel

theorem prime_128467 : Nat.Prime 128467 := by
  apply nodeValid_prime [2, 3, 13, 61] ⟨128467, 3, [(2, 1), (3, 4), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_129733 : Nat.Prime 129733 := by
  apply nodeValid_prime [2, 3, 19, 569] ⟨129733, 2, [(2, 2), (3, 1), (19, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_569
  · decide +kernel

theorem prime_144737 : Nat.Prime 144737 := by
  apply nodeValid_prime [2, 4523] ⟨144737, 3, [(2, 5), (4523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4523
  · decide +kernel

theorem prime_160159 : Nat.Prime 160159 := by
  apply nodeValid_prime [2, 3, 26693] ⟨160159, 3, [(2, 1), (3, 1), (26693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26693
  · decide +kernel

theorem prime_189271 : Nat.Prime 189271 := by
  apply nodeValid_prime [2, 3, 5, 701] ⟨189271, 3, [(2, 1), (3, 3), (5, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_701
  · decide +kernel

theorem prime_200639 : Nat.Prime 200639 := by
  apply nodeValid_prime [2, 43, 2333] ⟨200639, 17, [(2, 1), (43, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2333
  · decide +kernel

theorem prime_231709 : Nat.Prime 231709 := by
  apply nodeValid_prime [2, 3, 19309] ⟨231709, 6, [(2, 2), (3, 1), (19309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19309
  · decide +kernel

theorem prime_248621 : Nat.Prime 248621 := by
  apply nodeValid_prime [2, 5, 31, 401] ⟨248621, 2, [(2, 2), (5, 1), (31, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_401
  · decide +kernel

theorem prime_302551 : Nat.Prime 302551 := by
  apply nodeValid_prime [2, 3, 5, 2017] ⟨302551, 7, [(2, 1), (3, 1), (5, 2), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2017
  · decide +kernel

theorem prime_314213 : Nat.Prime 314213 := by
  apply nodeValid_prime [2, 78553] ⟨314213, 2, [(2, 2), (78553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_78553
  · decide +kernel

theorem prime_330853 : Nat.Prime 330853 := by
  apply nodeValid_prime [2, 3, 79, 349] ⟨330853, 2, [(2, 2), (3, 1), (79, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_349
  · decide +kernel

theorem prime_336989 : Nat.Prime 336989 := by
  apply nodeValid_prime [2, 84247] ⟨336989, 2, [(2, 2), (84247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84247
  · decide +kernel

theorem prime_351457 : Nat.Prime 351457 := by
  apply nodeValid_prime [2, 3, 7, 523] ⟨351457, 5, [(2, 5), (3, 1), (7, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_523
  · decide +kernel

theorem prime_355967 : Nat.Prime 355967 := by
  apply nodeValid_prime [2, 13, 13691] ⟨355967, 5, [(2, 1), (13, 1), (13691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_13691
  · decide +kernel

theorem prime_372943 : Nat.Prime 372943 := by
  apply nodeValid_prime [2, 3, 20719] ⟨372943, 3, [(2, 1), (3, 2), (20719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20719
  · decide +kernel

theorem prime_374287 : Nat.Prime 374287 := by
  apply nodeValid_prime [2, 3, 11, 53, 107] ⟨374287, 7, [(2, 1), (3, 1), (11, 1), (53, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_107
  · decide +kernel

theorem prime_390367 : Nat.Prime 390367 := by
  apply nodeValid_prime [2, 3, 7229] ⟨390367, 3, [(2, 1), (3, 3), (7229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7229
  · decide +kernel

theorem prime_512663 : Nat.Prime 512663 := by
  apply nodeValid_prime [2, 29, 8839] ⟨512663, 5, [(2, 1), (29, 1), (8839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_8839
  · decide +kernel

theorem prime_518933 : Nat.Prime 518933 := by
  apply nodeValid_prime [2, 129733] ⟨518933, 2, [(2, 2), (129733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_129733
  · decide +kernel

theorem prime_601969 : Nat.Prime 601969 := by
  apply nodeValid_prime [2, 3, 12541] ⟨601969, 31, [(2, 4), (3, 1), (12541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12541
  · decide +kernel

theorem prime_624839 : Nat.Prime 624839 := by
  apply nodeValid_prime [2, 151, 2069] ⟨624839, 13, [(2, 1), (151, 1), (2069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_2069
  · decide +kernel

theorem prime_628427 : Nat.Prime 628427 := by
  apply nodeValid_prime [2, 314213] ⟨628427, 2, [(2, 1), (314213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_314213
  · decide +kernel

theorem prime_646193 : Nat.Prime 646193 := by
  apply nodeValid_prime [2, 40387] ⟨646193, 3, [(2, 4), (40387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40387
  · decide +kernel

theorem prime_673979 : Nat.Prime 673979 := by
  apply nodeValid_prime [2, 336989] ⟨673979, 2, [(2, 1), (336989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_336989
  · decide +kernel

theorem prime_859841 : Nat.Prime 859841 := by
  apply nodeValid_prime [2, 5, 2687] ⟨859841, 3, [(2, 6), (5, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2687
  · decide +kernel

theorem prime_859981 : Nat.Prime 859981 := by
  apply nodeValid_prime [2, 3, 5, 11, 1303] ⟨859981, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1303
  · decide +kernel

theorem prime_1025327 : Nat.Prime 1025327 := by
  apply nodeValid_prime [2, 512663] ⟨1025327, 5, [(2, 1), (512663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_512663
  · decide +kernel

theorem prime_1070789 : Nat.Prime 1070789 := by
  apply nodeValid_prime [2, 23, 103, 113] ⟨1070789, 3, [(2, 2), (23, 1), (103, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_103
    · exact prime_113
  · decide +kernel

theorem prime_1208021 : Nat.Prime 1208021 := by
  apply nodeValid_prime [2, 5, 11, 17, 19] ⟨1208021, 3, [(2, 2), (5, 1), (11, 1), (17, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_1253047 : Nat.Prime 1253047 := by
  apply nodeValid_prime [2, 3, 97, 2153] ⟨1253047, 5, [(2, 1), (3, 1), (97, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_2153
  · decide +kernel

theorem prime_1260971 : Nat.Prime 1260971 := by
  apply nodeValid_prime [2, 5, 126097] ⟨1260971, 2, [(2, 1), (5, 1), (126097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_126097
  · decide +kernel

theorem prime_1393261 : Nat.Prime 1393261 := by
  apply nodeValid_prime [2, 3, 5, 11, 2111] ⟨1393261, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (2111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_2111
  · decide +kernel

theorem prime_1444567 : Nat.Prime 1444567 := by
  apply nodeValid_prime [2, 3, 71, 3391] ⟨1444567, 3, [(2, 1), (3, 1), (71, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_3391
  · decide +kernel

theorem prime_1578323 : Nat.Prime 1578323 := by
  apply nodeValid_prime [2, 431, 1831] ⟨1578323, 2, [(2, 1), (431, 1), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_1831
  · decide +kernel

theorem prime_1659107 : Nat.Prime 1659107 := by
  apply nodeValid_prime [2, 41, 20233] ⟨1659107, 2, [(2, 1), (41, 1), (20233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_20233
  · decide +kernel

theorem prime_2021891 : Nat.Prime 2021891 := by
  apply nodeValid_prime [2, 5, 13, 103, 151] ⟨2021891, 2, [(2, 1), (5, 1), (13, 1), (103, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_103
    · exact prime_151
  · decide +kernel

theorem prime_2164417 : Nat.Prime 2164417 := by
  apply nodeValid_prime [2, 3, 11273] ⟨2164417, 5, [(2, 6), (3, 1), (11273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11273
  · decide +kernel

theorem prime_2345153 : Nat.Prime 2345153 := by
  apply nodeValid_prime [2, 36643] ⟨2345153, 3, [(2, 6), (36643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_36643
  · decide +kernel

theorem prime_3397001 : Nat.Prime 3397001 := by
  apply nodeValid_prime [2, 5, 43, 79] ⟨3397001, 3, [(2, 3), (5, 3), (43, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_79
  · decide +kernel

theorem prime_3677017 : Nat.Prime 3677017 := by
  apply nodeValid_prime [2, 3, 7, 43, 509] ⟨3677017, 10, [(2, 3), (3, 1), (7, 1), (43, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_509
  · decide +kernel

theorem prime_4226009 : Nat.Prime 4226009 := by
  apply nodeValid_prime [2, 53, 9967] ⟨4226009, 3, [(2, 3), (53, 1), (9967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_9967
  · decide +kernel

theorem prime_4274189 : Nat.Prime 4274189 := by
  apply nodeValid_prime [2, 641, 1667] ⟨4274189, 2, [(2, 2), (641, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_641
    · exact prime_1667
  · decide +kernel

theorem prime_4383227 : Nat.Prime 4383227 := by
  apply nodeValid_prime [2, 139, 15767] ⟨4383227, 2, [(2, 1), (139, 1), (15767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_15767
  · decide +kernel

theorem prime_4501817 : Nat.Prime 4501817 := by
  apply nodeValid_prime [2, 11, 51157] ⟨4501817, 3, [(2, 3), (11, 1), (51157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_51157
  · decide +kernel

theorem prime_4690307 : Nat.Prime 4690307 := by
  apply nodeValid_prime [2, 2345153] ⟨4690307, 2, [(2, 1), (2345153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2345153
  · decide +kernel

theorem prime_4901549 : Nat.Prime 4901549 := by
  apply nodeValid_prime [2, 613, 1999] ⟨4901549, 2, [(2, 2), (613, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_1999
  · decide +kernel

theorem prime_5174803 : Nat.Prime 5174803 := by
  apply nodeValid_prime [2, 3, 19, 15131] ⟨5174803, 2, [(2, 1), (3, 2), (19, 1), (15131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_15131
  · decide +kernel

theorem prime_5458487 : Nat.Prime 5458487 := by
  apply nodeValid_prime [2, 11, 47, 5279] ⟨5458487, 10, [(2, 1), (11, 1), (47, 1), (5279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_5279
  · decide +kernel

theorem prime_6535847 : Nat.Prime 6535847 := by
  apply nodeValid_prime [2, 29, 112687] ⟨6535847, 5, [(2, 1), (29, 1), (112687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_112687
  · decide +kernel

theorem prime_6654979 : Nat.Prime 6654979 := by
  apply nodeValid_prime [2, 3, 11, 19, 29, 61] ⟨6654979, 2, [(2, 1), (3, 2), (11, 1), (19, 1), (29, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_29
    · exact prime_61
  · decide +kernel

theorem prime_6900877 : Nat.Prime 6900877 := by
  apply nodeValid_prime [2, 3, 19, 59] ⟨6900877, 5, [(2, 2), (3, 4), (19, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_59
  · decide +kernel

theorem prime_8452019 : Nat.Prime 8452019 := by
  apply nodeValid_prime [2, 4226009] ⟨8452019, 2, [(2, 1), (4226009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4226009
  · decide +kernel

theorem prime_8518091 : Nat.Prime 8518091 := by
  apply nodeValid_prime [2, 5, 7, 121687] ⟨8518091, 2, [(2, 1), (5, 1), (7, 1), (121687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_121687
  · decide +kernel

theorem prime_8541959 : Nat.Prime 8541959 := by
  apply nodeValid_prime [2, 659, 6481] ⟨8541959, 17, [(2, 1), (659, 1), (6481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_659
    · exact prime_6481
  · decide +kernel

theorem prime_9208253 : Nat.Prime 9208253 := by
  apply nodeValid_prime [2, 131, 17573] ⟨9208253, 2, [(2, 2), (131, 1), (17573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_17573
  · decide +kernel

theorem prime_9429653 : Nat.Prime 9429653 := by
  apply nodeValid_prime [2, 71, 33203] ⟨9429653, 2, [(2, 2), (71, 1), (33203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_33203
  · decide +kernel

theorem prime_9469939 : Nat.Prime 9469939 := by
  apply nodeValid_prime [2, 3, 1578323] ⟨9469939, 3, [(2, 1), (3, 1), (1578323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1578323
  · decide +kernel

theorem prime_10319773 : Nat.Prime 10319773 := by
  apply nodeValid_prime [2, 3, 859981] ⟨10319773, 2, [(2, 2), (3, 1), (859981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_859981
  · decide +kernel

theorem prime_10543711 : Nat.Prime 10543711 := by
  apply nodeValid_prime [2, 3, 5, 351457] ⟨10543711, 21, [(2, 1), (3, 1), (5, 1), (351457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_351457
  · decide +kernel

theorem prime_17414909 : Nat.Prime 17414909 := by
  apply nodeValid_prime [2, 7, 67, 9283] ⟨17414909, 2, [(2, 2), (7, 1), (67, 1), (9283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_9283
  · decide +kernel

theorem prime_17883721 : Nat.Prime 17883721 := by
  apply nodeValid_prime [2, 3, 5, 29, 571] ⟨17883721, 17, [(2, 3), (3, 3), (5, 1), (29, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_571
  · decide +kernel

theorem prime_18416507 : Nat.Prime 18416507 := by
  apply nodeValid_prime [2, 9208253] ⟨18416507, 2, [(2, 1), (9208253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9208253
  · decide +kernel

theorem prime_26200091 : Nat.Prime 26200091 := by
  apply nodeValid_prime [2, 5, 7, 374287] ⟨26200091, 6, [(2, 1), (5, 1), (7, 1), (374287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_374287
  · decide +kernel

theorem prime_27140107 : Nat.Prime 27140107 := by
  apply nodeValid_prime [2, 3, 7, 646193] ⟨27140107, 3, [(2, 1), (3, 1), (7, 1), (646193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_646193
  · decide +kernel

theorem prime_28422739 : Nat.Prime 28422739 := by
  apply nodeValid_prime [2, 3, 233, 251] ⟨28422739, 2, [(2, 1), (3, 5), (233, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_251
  · decide +kernel

theorem prime_34829819 : Nat.Prime 34829819 := by
  apply nodeValid_prime [2, 17414909] ⟨34829819, 2, [(2, 1), (17414909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17414909
  · decide +kernel

theorem prime_37842653 : Nat.Prime 37842653 := by
  apply nodeValid_prime [2, 157, 60259] ⟨37842653, 2, [(2, 2), (157, 1), (60259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_60259
  · decide +kernel

theorem prime_40689983 : Nat.Prime 40689983 := by
  apply nodeValid_prime [2, 19, 1070789] ⟨40689983, 5, [(2, 1), (19, 1), (1070789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1070789
  · decide +kernel

theorem prime_42962243 : Nat.Prime 42962243 := by
  apply nodeValid_prime [2, 71, 302551] ⟨42962243, 2, [(2, 1), (71, 1), (302551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_302551
  · decide +kernel

theorem prime_68621687 : Nat.Prime 68621687 := by
  apply nodeValid_prime [2, 7, 4901549] ⟨68621687, 5, [(2, 1), (7, 1), (4901549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4901549
  · decide +kernel

theorem prime_74913481 : Nat.Prime 74913481 := by
  apply nodeValid_prime [2, 3, 5, 59, 3527] ⟨74913481, 13, [(2, 3), (3, 2), (5, 1), (59, 1), (3527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_3527
  · decide +kernel

theorem prime_117786419 : Nat.Prime 117786419 := by
  apply nodeValid_prime [2, 47, 1253047] ⟨117786419, 2, [(2, 1), (47, 1), (1253047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1253047
  · decide +kernel

theorem prime_119307473 : Nat.Prime 119307473 := by
  apply nodeValid_prime [2, 167, 44651] ⟨119307473, 3, [(2, 4), (167, 1), (44651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_44651
  · decide +kernel

theorem prime_119587427 : Nat.Prime 119587427 := by
  apply nodeValid_prime [2, 7, 8541959] ⟨119587427, 2, [(2, 1), (7, 1), (8541959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8541959
  · decide +kernel

theorem prime_181698761 : Nat.Prime 181698761 := by
  apply nodeValid_prime [2, 5, 59, 76991] ⟨181698761, 6, [(2, 3), (5, 1), (59, 1), (76991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_76991
  · decide +kernel

theorem prime_316083611 : Nat.Prime 316083611 := by
  apply nodeValid_prime [2, 5, 1019, 31019] ⟨316083611, 2, [(2, 1), (5, 1), (1019, 1), (31019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1019
    · exact prime_31019
  · decide +kernel

theorem prime_330568177 : Nat.Prime 330568177 := by
  apply nodeValid_prime [2, 3, 43, 160159] ⟨330568177, 5, [(2, 4), (3, 1), (43, 1), (160159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_160159
  · decide +kernel

theorem prime_344939831 : Nat.Prime 344939831 := by
  apply nodeValid_prime [2, 5, 2591, 13313] ⟨344939831, 11, [(2, 1), (5, 1), (2591, 1), (13313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2591
    · exact prime_13313
  · decide +kernel

theorem prime_630586963 : Nat.Prime 630586963 := by
  apply nodeValid_prime [2, 3, 29, 1208021] ⟨630586963, 2, [(2, 1), (3, 2), (29, 1), (1208021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1208021
  · decide +kernel

theorem prime_632167223 : Nat.Prime 632167223 := by
  apply nodeValid_prime [2, 316083611] ⟨632167223, 5, [(2, 1), (316083611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_316083611
  · decide +kernel

theorem prime_637362023 : Nat.Prime 637362023 := by
  apply nodeValid_prime [2, 11, 67, 109, 3967] ⟨637362023, 5, [(2, 1), (11, 1), (67, 1), (109, 1), (3967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_67
    · exact prime_109
    · exact prime_3967
  · decide +kernel

theorem prime_643561817 : Nat.Prime 643561817 := by
  apply nodeValid_prime [2, 163, 211, 2339] ⟨643561817, 3, [(2, 3), (163, 1), (211, 1), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_211
    · exact prime_2339
  · decide +kernel

theorem prime_689822257 : Nat.Prime 689822257 := by
  apply nodeValid_prime [2, 3, 23, 624839] ⟨689822257, 5, [(2, 4), (3, 1), (23, 1), (624839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_624839
  · decide +kernel

theorem prime_983956823 : Nat.Prime 983956823 := by
  apply nodeValid_prime [2, 1487, 330853] ⟨983956823, 5, [(2, 1), (1487, 1), (330853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1487
    · exact prime_330853
  · decide +kernel

theorem prime_984936893 : Nat.Prime 984936893 := by
  apply nodeValid_prime [2, 37, 6654979] ⟨984936893, 2, [(2, 2), (37, 1), (6654979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_6654979
  · decide +kernel

theorem prime_1138720789 : Nat.Prime 1138720789 := by
  apply nodeValid_prime [2, 3, 10543711] ⟨1138720789, 7, [(2, 2), (3, 3), (10543711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10543711
  · decide +kernel

theorem prime_1475935259 : Nat.Prime 1475935259 := by
  apply nodeValid_prime [2, 7, 557, 189271] ⟨1475935259, 2, [(2, 1), (7, 1), (557, 1), (189271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_557
    · exact prime_189271
  · decide +kernel

theorem prime_1657485631 : Nat.Prime 1657485631 := by
  apply nodeValid_prime [2, 3, 5, 18416507] ⟨1657485631, 3, [(2, 1), (3, 2), (5, 1), (18416507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18416507
  · decide +kernel

theorem prime_3824172139 : Nat.Prime 3824172139 := by
  apply nodeValid_prime [2, 3, 637362023] ⟨3824172139, 2, [(2, 1), (3, 1), (637362023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_637362023
  · decide +kernel

theorem prime_4795083277 : Nat.Prime 4795083277 := by
  apply nodeValid_prime [2, 3, 19, 709, 29663] ⟨4795083277, 2, [(2, 2), (3, 1), (19, 1), (709, 1), (29663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_709
    · exact prime_29663
  · decide +kernel

theorem prime_6464195887 : Nat.Prime 6464195887 := by
  apply nodeValid_prime [2, 3, 293, 3677017] ⟨6464195887, 5, [(2, 1), (3, 1), (293, 1), (3677017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_293
    · exact prime_3677017
  · decide +kernel

theorem prime_6673157213 : Nat.Prime 6673157213 := by
  apply nodeValid_prime [2, 41, 40689983] ⟨6673157213, 2, [(2, 2), (41, 1), (40689983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_40689983
  · decide +kernel

theorem prime_13364159513 : Nat.Prime 13364159513 := by
  apply nodeValid_prime [2, 11, 109, 1393261] ⟨13364159513, 3, [(2, 3), (11, 1), (109, 1), (1393261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_109
    · exact prime_1393261
  · decide +kernel

theorem prime_13395141713 : Nat.Prime 13395141713 := by
  apply nodeValid_prime [2, 191, 4383227] ⟨13395141713, 3, [(2, 4), (191, 1), (4383227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_4383227
  · decide +kernel

theorem prime_15104281991 : Nat.Prime 15104281991 := by
  apply nodeValid_prime [2, 5, 7, 19, 29, 263, 1489] ⟨15104281991, 13, [(2, 1), (5, 1), (7, 1), (19, 1), (29, 1), (263, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_29
    · exact prime_263
    · exact prime_1489
  · decide +kernel

theorem prime_15839521913 : Nat.Prime 15839521913 := by
  apply nodeValid_prime [2, 19, 53, 103483] ⟨15839521913, 3, [(2, 3), (19, 2), (53, 1), (103483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_53
    · exact prime_103483
  · decide +kernel

theorem prime_25170929617 : Nat.Prime 25170929617 := by
  apply nodeValid_prime [2, 3, 7, 74913481] ⟨25170929617, 5, [(2, 4), (3, 1), (7, 1), (74913481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_74913481
  · decide +kernel

theorem prime_40034184623 : Nat.Prime 40034184623 := by
  apply nodeValid_prime [2, 53, 1061, 355967] ⟨40034184623, 10, [(2, 1), (53, 1), (1061, 1), (355967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1061
    · exact prime_355967
  · decide +kernel

theorem prime_45532057693 : Nat.Prime 45532057693 := by
  apply nodeValid_prime [2, 3, 11, 344939831] ⟨45532057693, 5, [(2, 2), (3, 1), (11, 1), (344939831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_344939831
  · decide +kernel

theorem prime_62927325281 : Nat.Prime 62927325281 := by
  apply nodeValid_prime [2, 5, 9941, 39563] ⟨62927325281, 6, [(2, 5), (5, 1), (9941, 1), (39563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9941
    · exact prime_39563
  · decide +kernel

theorem prime_68198336579 : Nat.Prime 68198336579 := by
  apply nodeValid_prime [2, 6247, 5458487] ⟨68198336579, 2, [(2, 1), (6247, 1), (5458487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6247
    · exact prime_5458487
  · decide +kernel

theorem prime_115665844543 : Nat.Prime 115665844543 := by
  apply nodeValid_prime [2, 3, 29, 71, 139, 193, 349] ⟨115665844543, 3, [(2, 1), (3, 1), (29, 1), (71, 1), (139, 1), (193, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_71
    · exact prime_139
    · exact prime_193
    · exact prime_349
  · decide +kernel

theorem prime_131710138423 : Nat.Prime 131710138423 := by
  apply nodeValid_prime [2, 3, 3181, 6900877] ⟨131710138423, 3, [(2, 1), (3, 1), (3181, 1), (6900877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3181
    · exact prime_6900877
  · decide +kernel

theorem prime_136396673159 : Nat.Prime 136396673159 := by
  apply nodeValid_prime [2, 68198336579] ⟨136396673159, 13, [(2, 1), (68198336579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68198336579
  · decide +kernel

theorem prime_167194953521 : Nat.Prime 167194953521 := by
  apply nodeValid_prime [2, 5, 7, 10091, 29587] ⟨167194953521, 3, [(2, 4), (5, 1), (7, 1), (10091, 1), (29587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_10091
    · exact prime_29587
  · decide +kernel

theorem prime_177159266923 : Nat.Prime 177159266923 := by
  apply nodeValid_prime [2, 3, 11, 31, 2287, 37861] ⟨177159266923, 2, [(2, 1), (3, 1), (11, 1), (31, 1), (2287, 1), (37861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_2287
    · exact prime_37861
  · decide +kernel

theorem prime_273192346159 : Nat.Prime 273192346159 := by
  apply nodeValid_prime [2, 3, 45532057693] ⟨273192346159, 3, [(2, 1), (3, 1), (45532057693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45532057693
  · decide +kernel

theorem prime_499390358833 : Nat.Prime 499390358833 := by
  apply nodeValid_prime [2, 3, 1663, 231709] ⟨499390358833, 10, [(2, 4), (3, 4), (1663, 1), (231709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1663
    · exact prime_231709
  · decide +kernel

theorem prime_602781378517 : Nat.Prime 602781378517 := by
  apply nodeValid_prime [2, 3, 17, 984936893] ⟨602781378517, 2, [(2, 2), (3, 2), (17, 1), (984936893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_984936893
  · decide +kernel

theorem prime_604102310809 : Nat.Prime 604102310809 := by
  apply nodeValid_prime [2, 3, 25170929617] ⟨604102310809, 11, [(2, 3), (3, 1), (25170929617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25170929617
  · decide +kernel

theorem prime_606308254891 : Nat.Prime 606308254891 := by
  apply nodeValid_prime [2, 3, 5, 13, 119587427] ⟨606308254891, 2, [(2, 1), (3, 1), (5, 1), (13, 2), (119587427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_119587427
  · decide +kernel

theorem prime_755678852609 : Nat.Prime 755678852609 := by
  apply nodeValid_prime [2, 1475935259] ⟨755678852609, 3, [(2, 9), (1475935259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1475935259
  · decide +kernel

theorem prime_1000242272651 : Nat.Prime 1000242272651 := by
  apply nodeValid_prime [2, 5, 29, 689822257] ⟨1000242272651, 2, [(2, 1), (5, 2), (29, 1), (689822257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_689822257
  · decide +kernel

theorem prime_1003902497363 : Nat.Prime 1003902497363 := by
  apply nodeValid_prime [2, 53, 15733, 601969] ⟨1003902497363, 2, [(2, 1), (53, 1), (15733, 1), (601969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_15733
    · exact prime_601969
  · decide +kernel

theorem prime_1511357705219 : Nat.Prime 1511357705219 := by
  apply nodeValid_prime [2, 755678852609] ⟨1511357705219, 2, [(2, 1), (755678852609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_755678852609
  · decide +kernel

theorem prime_3022715410439 : Nat.Prime 3022715410439 := by
  apply nodeValid_prime [2, 1511357705219] ⟨3022715410439, 7, [(2, 1), (1511357705219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1511357705219
  · decide +kernel

theorem prime_3042598037621 : Nat.Prime 3042598037621 := by
  apply nodeValid_prime [2, 5, 47, 719, 4501817] ⟨3042598037621, 2, [(2, 2), (5, 1), (47, 1), (719, 1), (4501817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_719
    · exact prime_4501817
  · decide +kernel

theorem prime_3047028383981 : Nat.Prime 3047028383981 := by
  apply nodeValid_prime [2, 5, 7, 1217, 17883721] ⟨3047028383981, 2, [(2, 2), (5, 1), (7, 1), (1217, 1), (17883721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1217
    · exact prime_17883721
  · decide +kernel

theorem prime_5992684305997 : Nat.Prime 5992684305997 := by
  apply nodeValid_prime [2, 3, 499390358833] ⟨5992684305997, 2, [(2, 2), (3, 1), (499390358833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_499390358833
  · decide +kernel

theorem prime_5992684379573 : Nat.Prime 5992684379573 := by
  apply nodeValid_prime [2, 11, 23, 163, 251, 144737] ⟨5992684379573, 2, [(2, 2), (11, 1), (23, 1), (163, 1), (251, 1), (144737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_163
    · exact prime_251
    · exact prime_144737
  · decide +kernel

theorem prime_5992684379639 : Nat.Prime 5992684379639 := by
  apply nodeValid_prime [2, 11, 229, 13649, 87149] ⟨5992684379639, 11, [(2, 1), (11, 1), (229, 1), (13649, 1), (87149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_229
    · exact prime_13649
    · exact prime_87149
  · decide +kernel

theorem prime_5997067890053 : Nat.Prime 5997067890053 := by
  apply nodeValid_prime [2, 19, 199, 239, 1659107] ⟨5997067890053, 2, [(2, 2), (19, 1), (199, 1), (239, 1), (1659107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_199
    · exact prime_239
    · exact prime_1659107
  · decide +kernel

theorem prime_5997067895059 : Nat.Prime 5997067895059 := by
  apply nodeValid_prime [2, 3, 28697, 34829819] ⟨5997067895059, 10, [(2, 1), (3, 1), (28697, 1), (34829819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28697
    · exact prime_34829819
  · decide +kernel

theorem prime_5997067896089 : Nat.Prime 5997067896089 := by
  apply nodeValid_prime [2, 518933, 1444567] ⟨5997067896089, 3, [(2, 3), (518933, 1), (1444567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_518933
    · exact prime_1444567
  · decide +kernel

theorem prime_6001453618997 : Nat.Prime 6001453618997 := by
  apply nodeValid_prime [2, 11, 136396673159] ⟨6001453618997, 2, [(2, 2), (11, 1), (136396673159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_136396673159
  · decide +kernel

theorem prime_6001453620889 : Nat.Prime 6001453620889 := by
  apply nodeValid_prime [2, 3, 11, 193, 117786419] ⟨6001453620889, 7, [(2, 3), (3, 1), (11, 1), (193, 1), (117786419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193
    · exact prime_117786419
  · decide +kernel

theorem prime_6001453635907 : Nat.Prime 6001453635907 := by
  apply nodeValid_prime [2, 3, 1000242272651] ⟨6001453635907, 3, [(2, 1), (3, 1), (1000242272651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1000242272651
  · decide +kernel

theorem prime_6005841491701 : Nat.Prime 6005841491701 := by
  apply nodeValid_prime [2, 3, 5, 6673157213] ⟨6005841491701, 2, [(2, 2), (3, 2), (5, 2), (6673157213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6673157213
  · decide +kernel

theorem prime_6005841492349 : Nat.Prime 6005841492349 := by
  apply nodeValid_prime [2, 3, 251, 773, 859841] ⟨6005841492349, 7, [(2, 2), (3, 2), (251, 1), (773, 1), (859841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_773
    · exact prime_859841
  · decide +kernel

theorem prime_6005841554653 : Nat.Prime 6005841554653 := by
  apply nodeValid_prime [2, 3, 97, 643, 1553, 5167] ⟨6005841554653, 2, [(2, 2), (3, 1), (97, 1), (643, 1), (1553, 1), (5167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_643
    · exact prime_1553
    · exact prime_5167
  · decide +kernel

theorem prime_6010231615499 : Nat.Prime 6010231615499 := by
  apply nodeValid_prime [2, 11, 273192346159] ⟨6010231615499, 2, [(2, 1), (11, 1), (273192346159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_273192346159
  · decide +kernel

theorem prime_6010231616359 : Nat.Prime 6010231616359 := by
  apply nodeValid_prime [2, 3, 37, 149, 181698761] ⟨6010231616359, 15, [(2, 1), (3, 1), (37, 1), (149, 1), (181698761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_149
    · exact prime_181698761
  · decide +kernel

theorem prime_6010231647793 : Nat.Prime 6010231647793 := by
  apply nodeValid_prime [2, 3, 109, 911, 1260971] ⟨6010231647793, 10, [(2, 4), (3, 1), (109, 1), (911, 1), (1260971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_911
    · exact prime_1260971
  · decide +kernel

theorem prime_6014623916237 : Nat.Prime 6014623916237 := by
  apply nodeValid_prime [2, 13, 115665844543] ⟨6014623916237, 2, [(2, 2), (13, 1), (115665844543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_115665844543
  · decide +kernel

theorem prime_6014624054339 : Nat.Prime 6014624054339 := by
  apply nodeValid_prime [2, 37, 59, 3529, 390367] ⟨6014624054339, 2, [(2, 1), (37, 1), (59, 1), (3529, 1), (390367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_59
    · exact prime_3529
    · exact prime_390367
  · decide +kernel

theorem prime_6014624055101 : Nat.Prime 6014624055101 := by
  apply nodeValid_prime [2, 5, 23, 307, 8518091] ⟨6014624055101, 2, [(2, 2), (5, 2), (23, 1), (307, 1), (8518091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_307
    · exact prime_8518091
  · decide +kernel

theorem prime_6019018326757 : Nat.Prime 6019018326757 := by
  apply nodeValid_prime [2, 3, 167194953521] ⟨6019018326757, 2, [(2, 2), (3, 2), (167194953521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167194953521
  · decide +kernel

theorem prime_6019018326941 : Nat.Prime 6019018326941 := by
  apply nodeValid_prime [2, 5, 19, 15839521913] ⟨6019018326941, 2, [(2, 2), (5, 1), (19, 1), (15839521913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_15839521913
  · decide +kernel

theorem prime_6019018362629 : Nat.Prime 6019018362629 := by
  apply nodeValid_prime [2, 17, 29, 467, 6535847] ⟨6019018362629, 2, [(2, 2), (17, 1), (29, 1), (467, 1), (6535847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_467
    · exact prime_6535847
  · decide +kernel

theorem prime_6023414984179 : Nat.Prime 6023414984179 := by
  apply nodeValid_prime [2, 3, 1003902497363] ⟨6023414984179, 10, [(2, 1), (3, 1), (1003902497363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1003902497363
  · decide +kernel

theorem prime_6023415075383 : Nat.Prime 6023415075383 := by
  apply nodeValid_prime [2, 17, 177159266923] ⟨6023415075383, 5, [(2, 1), (17, 1), (177159266923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_177159266923
  · decide +kernel

theorem prime_6023415078011 : Nat.Prime 6023415078011 := by
  apply nodeValid_prime [2, 5, 11, 1447, 37842653] ⟨6023415078011, 2, [(2, 1), (5, 1), (11, 1), (1447, 1), (37842653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1447
    · exact prime_37842653
  · decide +kernel

theorem prime_6027813770851 : Nat.Prime 6027813770851 := by
  apply nodeValid_prime [2, 3, 5, 13395141713] ⟨6027813770851, 2, [(2, 1), (3, 2), (5, 2), (13395141713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13395141713
  · decide +kernel

theorem prime_6027813772429 : Nat.Prime 6027813772429 := by
  apply nodeValid_prime [2, 3, 7, 41, 37423, 46769] ⟨6027813772429, 6, [(2, 2), (3, 1), (7, 1), (41, 1), (37423, 1), (46769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_37423
    · exact prime_46769
  · decide +kernel

theorem prime_6027813785171 : Nat.Prime 6027813785171 := by
  apply nodeValid_prime [2, 5, 602781378517] ⟨6027813785171, 2, [(2, 1), (5, 1), (602781378517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_602781378517
  · decide +kernel

theorem prime_6032214743449 : Nat.Prime 6032214743449 := by
  apply nodeValid_prime [2, 3, 37, 239, 28422739] ⟨6032214743449, 7, [(2, 3), (3, 1), (37, 1), (239, 1), (28422739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_239
    · exact prime_28422739
  · decide +kernel

theorem prime_6032214747733 : Nat.Prime 6032214747733 := by
  apply nodeValid_prime [2, 3, 248621, 2021891] ⟨6032214747733, 2, [(2, 2), (3, 1), (248621, 1), (2021891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_248621
    · exact prime_2021891
  · decide +kernel

theorem prime_6032214762467 : Nat.Prime 6032214762467 := by
  apply nodeValid_prime [2, 17, 37, 4795083277] ⟨6032214762467, 2, [(2, 1), (17, 1), (37, 1), (4795083277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_4795083277
  · decide +kernel

theorem prime_6036617914219 : Nat.Prime 6036617914219 := by
  apply nodeValid_prime [2, 3, 39679, 8452019] ⟨6036617914219, 2, [(2, 1), (3, 2), (39679, 1), (8452019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39679
    · exact prime_8452019
  · decide +kernel

theorem prime_6036618081649 : Nat.Prime 6036618081649 := by
  apply nodeValid_prime [2, 3, 7, 11, 211, 2087, 3709] ⟨6036618081649, 38, [(2, 4), (3, 1), (7, 1), (11, 1), (211, 1), (2087, 1), (3709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_211
    · exact prime_2087
    · exact prime_3709
  · decide +kernel

theorem prime_6036618081881 : Nat.Prime 6036618081881 := by
  apply nodeValid_prime [2, 5, 163, 7207, 128467] ⟨6036618081881, 3, [(2, 3), (5, 1), (163, 1), (7207, 1), (128467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_7207
    · exact prime_128467
  · decide +kernel

theorem prime_6041023105541 : Nat.Prime 6041023105541 := by
  apply nodeValid_prime [2, 5, 479, 630586963] ⟨6041023105541, 2, [(2, 2), (5, 1), (479, 1), (630586963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479
    · exact prime_630586963
  · decide +kernel

theorem prime_6041023108091 : Nat.Prime 6041023108091 := by
  apply nodeValid_prime [2, 5, 604102310809] ⟨6041023108091, 2, [(2, 1), (5, 1), (604102310809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_604102310809
  · decide +kernel

theorem prime_6041023226977 : Nat.Prime 6041023226977 := by
  apply nodeValid_prime [2, 3, 62927325281] ⟨6041023226977, 10, [(2, 5), (3, 1), (62927325281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62927325281
  · decide +kernel

theorem prime_6045430720513 : Nat.Prime 6045430720513 := by
  apply nodeValid_prime [2, 3, 983956823] ⟨6045430720513, 10, [(2, 11), (3, 1), (983956823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_983956823
  · decide +kernel

theorem prime_6045430820879 : Nat.Prime 6045430820879 := by
  apply nodeValid_prime [2, 3022715410439] ⟨6045430820879, 7, [(2, 1), (3022715410439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3022715410439
  · decide +kernel

theorem prime_6045430820977 : Nat.Prime 6045430820977 := by
  apply nodeValid_prime [2, 3, 127, 330568177] ⟨6045430820977, 5, [(2, 4), (3, 2), (127, 1), (330568177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_330568177
  · decide +kernel

theorem prime_6049840323899 : Nat.Prime 6049840323899 := by
  apply nodeValid_prime [2, 7, 113, 3824172139] ⟨6049840323899, 2, [(2, 1), (7, 1), (113, 1), (3824172139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_3824172139
  · decide +kernel

theorem prime_6049840324111 : Nat.Prime 6049840324111 := by
  apply nodeValid_prime [2, 3, 5, 11, 29, 632167223] ⟨6049840324111, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (632167223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_632167223
  · decide +kernel

theorem prime_6049840386829 : Nat.Prime 6049840386829 := by
  apply nodeValid_prime [2, 3, 7, 37, 97, 1283, 15641] ⟨6049840386829, 2, [(2, 2), (3, 1), (7, 1), (37, 1), (97, 1), (1283, 1), (15641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_97
    · exact prime_1283
    · exact prime_15641
  · decide +kernel

theorem prime_6054252130429 : Nat.Prime 6054252130429 := by
  apply nodeValid_prime [2, 3, 41, 61331, 200639] ⟨6054252130429, 2, [(2, 2), (3, 1), (41, 1), (61331, 1), (200639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_61331
    · exact prime_200639
  · decide +kernel

theorem prime_6054252130733 : Nat.Prime 6054252130733 := by
  apply nodeValid_prime [2, 13, 12347, 9429653] ⟨6054252130733, 2, [(2, 2), (13, 1), (12347, 1), (9429653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_12347
    · exact prime_9429653
  · decide +kernel

theorem prime_6054252228919 : Nat.Prime 6054252228919 := by
  apply nodeValid_prime [2, 3, 17, 27140107] ⟨6054252228919, 3, [(2, 1), (3, 8), (17, 1), (27140107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_27140107
  · decide +kernel

theorem prime_6058666243387 : Nat.Prime 6058666243387 := by
  apply nodeValid_prime [2, 3, 29, 443, 26200091] ⟨6058666243387, 3, [(2, 1), (3, 2), (29, 1), (443, 1), (26200091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_443
    · exact prime_26200091
  · decide +kernel

theorem prime_6058666367459 : Nat.Prime 6058666367459 := by
  apply nodeValid_prime [2, 23, 131710138423] ⟨6058666367459, 2, [(2, 1), (23, 1), (131710138423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_131710138423
  · decide +kernel

theorem prime_6058666368239 : Nat.Prime 6058666368239 := by
  apply nodeValid_prime [2, 11, 43, 269, 2164417] ⟨6058666368239, 7, [(2, 1), (11, 2), (43, 1), (269, 1), (2164417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_269
    · exact prime_2164417
  · decide +kernel

theorem prime_6063082438199 : Nat.Prime 6063082438199 := by
  apply nodeValid_prime [2, 31, 59, 1657485631] ⟨6063082438199, 13, [(2, 1), (31, 1), (59, 1), (1657485631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_59
    · exact prime_1657485631
  · decide +kernel

theorem prime_6063082548811 : Nat.Prime 6063082548811 := by
  apply nodeValid_prime [2, 3, 5, 7, 45943, 628427] ⟨6063082548811, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (45943, 1), (628427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_45943
    · exact prime_628427
  · decide +kernel

theorem prime_6063082548911 : Nat.Prime 6063082548911 := by
  apply nodeValid_prime [2, 5, 606308254891] ⟨6063082548911, 11, [(2, 1), (5, 1), (606308254891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_606308254891
  · decide +kernel

theorem prime_6067500810677 : Nat.Prime 6067500810677 := by
  apply nodeValid_prime [2, 2357, 643561817] ⟨6067500810677, 2, [(2, 2), (2357, 1), (643561817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2357
    · exact prime_643561817
  · decide +kernel

theorem prime_6067500846647 : Nat.Prime 6067500846647 := by
  apply nodeValid_prime [2, 251, 347, 373, 93383] ⟨6067500846647, 5, [(2, 1), (251, 1), (347, 1), (373, 1), (93383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_347
    · exact prime_373
    · exact prime_93383
  · decide +kernel

theorem prime_6067500846889 : Nat.Prime 6067500846889 := by
  apply nodeValid_prime [2, 3, 13, 163, 119307473] ⟨6067500846889, 7, [(2, 3), (3, 1), (13, 1), (163, 1), (119307473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_163
    · exact prime_119307473
  · decide +kernel

theorem prime_6071921352377 : Nat.Prime 6071921352377 := by
  apply nodeValid_prime [2, 11, 47, 313, 4690307] ⟨6071921352377, 3, [(2, 3), (11, 1), (47, 1), (313, 1), (4690307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_313
    · exact prime_4690307
  · decide +kernel

theorem prime_6071921352509 : Nat.Prime 6071921352509 := by
  apply nodeValid_prime [2, 11, 2011, 68621687] ⟨6071921352509, 2, [(2, 2), (11, 1), (2011, 1), (68621687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2011
    · exact prime_68621687
  · decide +kernel

theorem prime_6071921360383 : Nat.Prime 6071921360383 := by
  apply nodeValid_prime [2, 3, 67, 15104281991] ⟨6071921360383, 6, [(2, 1), (3, 1), (67, 1), (15104281991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_15104281991
  · decide +kernel

theorem prime_6076344083101 : Nat.Prime 6076344083101 := by
  apply nodeValid_prime [2, 3, 5, 1093, 4261, 4349] ⟨6076344083101, 2, [(2, 2), (3, 1), (5, 2), (1093, 1), (4261, 1), (4349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1093
    · exact prime_4261
    · exact prime_4349
  · decide +kernel

theorem prime_6076344133751 : Nat.Prime 6076344133751 := by
  apply nodeValid_prime [2, 5, 11, 431, 1025327] ⟨6076344133751, 13, [(2, 1), (5, 4), (11, 1), (431, 1), (1025327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_431
    · exact prime_1025327
  · decide +kernel

theorem prime_6076344133781 : Nat.Prime 6076344133781 := by
  apply nodeValid_prime [2, 5, 47, 6464195887] ⟨6076344133781, 2, [(2, 2), (5, 1), (47, 1), (6464195887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_6464195887
  · decide +kernel

theorem prime_6080768985391 : Nat.Prime 6080768985391 := by
  apply nodeValid_prime [2, 3, 5, 11, 227, 1913, 42433] ⟨6080768985391, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (227, 1), (1913, 1), (42433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_227
    · exact prime_1913
    · exact prime_42433
  · decide +kernel

theorem prime_6080769013009 : Nat.Prime 6080769013009 := by
  apply nodeValid_prime [2, 3, 107, 277, 4274189] ⟨6080769013009, 7, [(2, 4), (3, 1), (107, 1), (277, 1), (4274189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_277
    · exact prime_4274189
  · decide +kernel

theorem prime_6080769013261 : Nat.Prime 6080769013261 := by
  apply nodeValid_prime [2, 3, 5, 89, 1138720789] ⟨6080769013261, 7, [(2, 2), (3, 1), (5, 1), (89, 1), (1138720789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_1138720789
  · decide +kernel

theorem prime_6085196062697 : Nat.Prime 6085196062697 := by
  apply nodeValid_prime [2, 19, 40034184623] ⟨6085196062697, 3, [(2, 3), (19, 1), (40034184623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_40034184623
  · decide +kernel

theorem prime_6085196064557 : Nat.Prime 6085196064557 := by
  apply nodeValid_prime [2, 7, 149, 3911, 372943] ⟨6085196064557, 2, [(2, 2), (7, 1), (149, 1), (3911, 1), (372943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_149
    · exact prime_3911
    · exact prime_372943
  · decide +kernel

theorem prime_6085196075243 : Nat.Prime 6085196075243 := by
  apply nodeValid_prime [2, 3042598037621] ⟨6085196075243, 2, [(2, 1), (3042598037621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3042598037621
  · decide +kernel

theorem prime_6089625334073 : Nat.Prime 6089625334073 := by
  apply nodeValid_prime [2, 7, 11483, 9469939] ⟨6089625334073, 3, [(2, 3), (7, 1), (11483, 1), (9469939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11483
    · exact prime_9469939
  · decide +kernel

theorem prime_6089625373553 : Nat.Prime 6089625373553 := by
  apply nodeValid_prime [2, 7, 19, 79, 5174803] ⟨6089625373553, 3, [(2, 4), (7, 2), (19, 1), (79, 1), (5174803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_79
    · exact prime_5174803
  · decide +kernel

theorem prime_6089625373987 : Nat.Prime 6089625373987 := by
  apply nodeValid_prime [2, 3, 7, 11, 41, 53, 673979] ⟨6089625373987, 2, [(2, 1), (3, 3), (7, 1), (11, 1), (41, 1), (53, 1), (673979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_41
    · exact prime_53
    · exact prime_673979
  · decide +kernel

theorem prime_6094056737929 : Nat.Prime 6094056737929 := by
  apply nodeValid_prime [2, 3, 19, 13364159513] ⟨6094056737929, 14, [(2, 3), (3, 1), (19, 1), (13364159513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_13364159513
  · decide +kernel

theorem prime_6094056737953 : Nat.Prime 6094056737953 := by
  apply nodeValid_prime [2, 3, 6229, 3397001] ⟨6094056737953, 5, [(2, 5), (3, 2), (6229, 1), (3397001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6229
    · exact prime_3397001
  · decide +kernel

theorem prime_6094056767963 : Nat.Prime 6094056767963 := by
  apply nodeValid_prime [2, 3047028383981] ⟨6094056767963, 2, [(2, 1), (3047028383981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3047028383981
  · decide +kernel

theorem prime_6098490393851 : Nat.Prime 6098490393851 := by
  apply nodeValid_prime [2, 5, 17, 167, 42962243] ⟨6098490393851, 2, [(2, 1), (5, 2), (17, 1), (167, 1), (42962243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_167
    · exact prime_42962243
  · decide +kernel

theorem prime_6098490493369 : Nat.Prime 6098490493369 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 127, 647, 1999] ⟨6098490493369, 19, [(2, 3), (3, 1), (7, 1), (13, 1), (17, 1), (127, 1), (647, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_127
    · exact prime_647
    · exact prime_1999
  · decide +kernel

theorem prime_6098490493897 : Nat.Prime 6098490493897 := by
  apply nodeValid_prime [2, 3, 24623, 10319773] ⟨6098490493897, 5, [(2, 3), (3, 1), (24623, 1), (10319773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24623
    · exact prime_10319773
  · decide +kernel

end Sude.Lucas.Generated
