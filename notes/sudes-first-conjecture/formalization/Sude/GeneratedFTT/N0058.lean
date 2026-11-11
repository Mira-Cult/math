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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0054

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3947 : Nat.Prime 3947 := by
  apply nodeValid_prime [2, 1973] ⟨3947, 2, [(2, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1973
  · decide +kernel

theorem prime_4289 : Nat.Prime 4289 := by
  apply nodeValid_prime [2, 67] ⟨4289, 3, [(2, 6), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67
  · decide +kernel

theorem prime_9623 : Nat.Prime 9623 := by
  apply nodeValid_prime [2, 17, 283] ⟨9623, 5, [(2, 1), (17, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_283
  · decide +kernel

theorem prime_11003 : Nat.Prime 11003 := by
  apply nodeValid_prime [2, 5501] ⟨11003, 2, [(2, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5501
  · decide +kernel

theorem prime_12401 : Nat.Prime 12401 := by
  apply nodeValid_prime [2, 5, 31] ⟨12401, 3, [(2, 4), (5, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_14983 : Nat.Prime 14983 := by
  apply nodeValid_prime [2, 3, 11, 227] ⟨14983, 3, [(2, 1), (3, 1), (11, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_227
  · decide +kernel

theorem prime_15199 : Nat.Prime 15199 := by
  apply nodeValid_prime [2, 3, 17, 149] ⟨15199, 6, [(2, 1), (3, 1), (17, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_149
  · decide +kernel

theorem prime_15383 : Nat.Prime 15383 := by
  apply nodeValid_prime [2, 7691] ⟨15383, 5, [(2, 1), (7691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7691
  · decide +kernel

theorem prime_17863 : Nat.Prime 17863 := by
  apply nodeValid_prime [2, 3, 13, 229] ⟨17863, 6, [(2, 1), (3, 1), (13, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_229
  · decide +kernel

theorem prime_18691 : Nat.Prime 18691 := by
  apply nodeValid_prime [2, 3, 5, 7, 89] ⟨18691, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_19661 : Nat.Prime 19661 := by
  apply nodeValid_prime [2, 5, 983] ⟨19661, 2, [(2, 2), (5, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_983
  · decide +kernel

theorem prime_19717 : Nat.Prime 19717 := by
  apply nodeValid_prime [2, 3, 31, 53] ⟨19717, 2, [(2, 2), (3, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_23431 : Nat.Prime 23431 := by
  apply nodeValid_prime [2, 3, 5, 11, 71] ⟨23431, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_23509 : Nat.Prime 23509 := by
  apply nodeValid_prime [2, 3, 653] ⟨23509, 2, [(2, 2), (3, 2), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
  · decide +kernel

theorem prime_25453 : Nat.Prime 25453 := by
  apply nodeValid_prime [2, 3, 7, 101] ⟨25453, 2, [(2, 2), (3, 2), (7, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
  · decide +kernel

theorem prime_28097 : Nat.Prime 28097 := by
  apply nodeValid_prime [2, 439] ⟨28097, 3, [(2, 6), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_439
  · decide +kernel

theorem prime_28283 : Nat.Prime 28283 := by
  apply nodeValid_prime [2, 79, 179] ⟨28283, 2, [(2, 1), (79, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_179
  · decide +kernel

theorem prime_29873 : Nat.Prime 29873 := by
  apply nodeValid_prime [2, 1867] ⟨29873, 3, [(2, 4), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1867
  · decide +kernel

theorem prime_39113 : Nat.Prime 39113 := by
  apply nodeValid_prime [2, 4889] ⟨39113, 3, [(2, 3), (4889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4889
  · decide +kernel

theorem prime_39451 : Nat.Prime 39451 := by
  apply nodeValid_prime [2, 3, 5, 263] ⟨39451, 2, [(2, 1), (3, 1), (5, 2), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_40849 : Nat.Prime 40849 := by
  apply nodeValid_prime [2, 3, 23, 37] ⟨40849, 11, [(2, 4), (3, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_45697 : Nat.Prime 45697 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨45697, 10, [(2, 7), (3, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_50273 : Nat.Prime 50273 := by
  apply nodeValid_prime [2, 1571] ⟨50273, 3, [(2, 5), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1571
  · decide +kernel

theorem prime_51767 : Nat.Prime 51767 := by
  apply nodeValid_prime [2, 11, 13, 181] ⟨51767, 5, [(2, 1), (11, 1), (13, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_181
  · decide +kernel

theorem prime_56533 : Nat.Prime 56533 := by
  apply nodeValid_prime [2, 3, 7, 673] ⟨56533, 5, [(2, 2), (3, 1), (7, 1), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_673
  · decide +kernel

theorem prime_57077 : Nat.Prime 57077 := by
  apply nodeValid_prime [2, 19, 751] ⟨57077, 2, [(2, 2), (19, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_751
  · decide +kernel

theorem prime_59747 : Nat.Prime 59747 := by
  apply nodeValid_prime [2, 29873] ⟨59747, 2, [(2, 1), (29873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29873
  · decide +kernel

theorem prime_64189 : Nat.Prime 64189 := by
  apply nodeValid_prime [2, 3, 1783] ⟨64189, 2, [(2, 2), (3, 2), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1783
  · decide +kernel

theorem prime_71843 : Nat.Prime 71843 := by
  apply nodeValid_prime [2, 17, 2113] ⟨71843, 2, [(2, 1), (17, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2113
  · decide +kernel

theorem prime_74687 : Nat.Prime 74687 := by
  apply nodeValid_prime [2, 107, 349] ⟨74687, 5, [(2, 1), (107, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_349
  · decide +kernel

theorem prime_84061 : Nat.Prime 84061 := by
  apply nodeValid_prime [2, 3, 5, 467] ⟨84061, 7, [(2, 2), (3, 2), (5, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
  · decide +kernel

theorem prime_89899 : Nat.Prime 89899 := by
  apply nodeValid_prime [2, 3, 14983] ⟨89899, 2, [(2, 1), (3, 1), (14983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14983
  · decide +kernel

theorem prime_97583 : Nat.Prime 97583 := by
  apply nodeValid_prime [2, 97, 503] ⟨97583, 5, [(2, 1), (97, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_503
  · decide +kernel

theorem prime_100547 : Nat.Prime 100547 := by
  apply nodeValid_prime [2, 50273] ⟨100547, 2, [(2, 1), (50273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_50273
  · decide +kernel

theorem prime_106921 : Nat.Prime 106921 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨106921, 14, [(2, 3), (3, 5), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_115331 : Nat.Prime 115331 := by
  apply nodeValid_prime [2, 5, 19, 607] ⟨115331, 6, [(2, 1), (5, 1), (19, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_607
  · decide +kernel

theorem prime_121321 : Nat.Prime 121321 := by
  apply nodeValid_prime [2, 3, 5, 337] ⟨121321, 13, [(2, 3), (3, 2), (5, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_337
  · decide +kernel

theorem prime_128483 : Nat.Prime 128483 := by
  apply nodeValid_prime [2, 227, 283] ⟨128483, 2, [(2, 1), (227, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_283
  · decide +kernel

theorem prime_142217 : Nat.Prime 142217 := by
  apply nodeValid_prime [2, 29, 613] ⟨142217, 3, [(2, 3), (29, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_613
  · decide +kernel

theorem prime_153259 : Nat.Prime 153259 := by
  apply nodeValid_prime [2, 3, 7, 41, 89] ⟨153259, 7, [(2, 1), (3, 1), (7, 1), (41, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_89
  · decide +kernel

theorem prime_156719 : Nat.Prime 156719 := by
  apply nodeValid_prime [2, 127, 617] ⟨156719, 19, [(2, 1), (127, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_617
  · decide +kernel

theorem prime_195929 : Nat.Prime 195929 := by
  apply nodeValid_prime [2, 19, 1289] ⟨195929, 3, [(2, 3), (19, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1289
  · decide +kernel

theorem prime_209449 : Nat.Prime 209449 := by
  apply nodeValid_prime [2, 3, 2909] ⟨209449, 13, [(2, 3), (3, 2), (2909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2909
  · decide +kernel

theorem prime_211219 : Nat.Prime 211219 := by
  apply nodeValid_prime [2, 3, 7, 47, 107] ⟨211219, 2, [(2, 1), (3, 1), (7, 1), (47, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_107
  · decide +kernel

theorem prime_226133 : Nat.Prime 226133 := by
  apply nodeValid_prime [2, 56533] ⟨226133, 2, [(2, 2), (56533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56533
  · decide +kernel

theorem prime_230663 : Nat.Prime 230663 := by
  apply nodeValid_prime [2, 115331] ⟨230663, 5, [(2, 1), (115331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115331
  · decide +kernel

theorem prime_236707 : Nat.Prime 236707 := by
  apply nodeValid_prime [2, 3, 39451] ⟨236707, 2, [(2, 1), (3, 1), (39451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39451
  · decide +kernel

theorem prime_241463 : Nat.Prime 241463 := by
  apply nodeValid_prime [2, 13, 37, 251] ⟨241463, 5, [(2, 1), (13, 1), (37, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_251
  · decide +kernel

theorem prime_288493 : Nat.Prime 288493 := by
  apply nodeValid_prime [2, 3, 29, 829] ⟨288493, 6, [(2, 2), (3, 1), (29, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_829
  · decide +kernel

theorem prime_294509 : Nat.Prime 294509 := by
  apply nodeValid_prime [2, 17, 61, 71] ⟨294509, 2, [(2, 2), (17, 1), (61, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_71
  · decide +kernel

theorem prime_295937 : Nat.Prime 295937 := by
  apply nodeValid_prime [2, 17] ⟨295937, 3, [(2, 10), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17
  · decide +kernel

theorem prime_303431 : Nat.Prime 303431 := by
  apply nodeValid_prime [2, 5, 19, 1597] ⟨303431, 7, [(2, 1), (5, 1), (19, 1), (1597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_1597
  · decide +kernel

theorem prime_308809 : Nat.Prime 308809 := by
  apply nodeValid_prime [2, 3, 4289] ⟨308809, 11, [(2, 3), (3, 2), (4289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4289
  · decide +kernel

theorem prime_357989 : Nat.Prime 357989 := by
  apply nodeValid_prime [2, 31, 2887] ⟨357989, 2, [(2, 2), (31, 1), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2887
  · decide +kernel

theorem prime_364349 : Nat.Prime 364349 := by
  apply nodeValid_prime [2, 79, 1153] ⟨364349, 2, [(2, 2), (79, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_1153
  · decide +kernel

theorem prime_394481 : Nat.Prime 394481 := by
  apply nodeValid_prime [2, 5, 4931] ⟨394481, 3, [(2, 4), (5, 1), (4931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4931
  · decide +kernel

theorem prime_408491 : Nat.Prime 408491 := by
  apply nodeValid_prime [2, 5, 40849] ⟨408491, 2, [(2, 1), (5, 1), (40849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40849
  · decide +kernel

theorem prime_408539 : Nat.Prime 408539 := by
  apply nodeValid_prime [2, 13, 19, 827] ⟨408539, 2, [(2, 1), (13, 1), (19, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_827
  · decide +kernel

theorem prime_412561 : Nat.Prime 412561 := by
  apply nodeValid_prime [2, 3, 5, 191] ⟨412561, 11, [(2, 4), (3, 3), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_518233 : Nat.Prime 518233 := by
  apply nodeValid_prime [2, 3, 11, 13, 151] ⟨518233, 5, [(2, 3), (3, 1), (11, 1), (13, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_151
  · decide +kernel

theorem prime_588083 : Nat.Prime 588083 := by
  apply nodeValid_prime [2, 11, 26731] ⟨588083, 2, [(2, 1), (11, 1), (26731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_26731
  · decide +kernel

theorem prime_625033 : Nat.Prime 625033 := by
  apply nodeValid_prime [2, 3, 8681] ⟨625033, 11, [(2, 3), (3, 2), (8681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8681
  · decide +kernel

theorem prime_667867 : Nat.Prime 667867 := by
  apply nodeValid_prime [2, 3, 79, 1409] ⟨667867, 2, [(2, 1), (3, 1), (79, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_1409
  · decide +kernel

theorem prime_678371 : Nat.Prime 678371 := by
  apply nodeValid_prime [2, 5, 7, 11, 881] ⟨678371, 2, [(2, 1), (5, 1), (7, 1), (11, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_881
  · decide +kernel

theorem prime_714521 : Nat.Prime 714521 := by
  apply nodeValid_prime [2, 5, 17863] ⟨714521, 3, [(2, 3), (5, 1), (17863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17863
  · decide +kernel

theorem prime_820747 : Nat.Prime 820747 := by
  apply nodeValid_prime [2, 3, 15199] ⟨820747, 2, [(2, 1), (3, 3), (15199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15199
  · decide +kernel

theorem prime_837797 : Nat.Prime 837797 := by
  apply nodeValid_prime [2, 209449] ⟨837797, 2, [(2, 2), (209449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_209449
  · decide +kernel

theorem prime_862117 : Nat.Prime 862117 := by
  apply nodeValid_prime [2, 3, 71843] ⟨862117, 14, [(2, 2), (3, 1), (71843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71843
  · decide +kernel

theorem prime_907811 : Nat.Prime 907811 := by
  apply nodeValid_prime [2, 5, 23, 3947] ⟨907811, 2, [(2, 1), (5, 1), (23, 1), (3947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_3947
  · decide +kernel

theorem prime_943729 : Nat.Prime 943729 := by
  apply nodeValid_prime [2, 3, 19661] ⟨943729, 11, [(2, 4), (3, 1), (19661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19661
  · decide +kernel

theorem prime_1046369 : Nat.Prime 1046369 := by
  apply nodeValid_prime [2, 19, 1721] ⟨1046369, 3, [(2, 5), (19, 1), (1721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1721
  · decide +kernel

theorem prime_1103579 : Nat.Prime 1103579 := by
  apply nodeValid_prime [2, 7, 11261] ⟨1103579, 2, [(2, 1), (7, 2), (11261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11261
  · decide +kernel

theorem prime_1107317 : Nat.Prime 1107317 := by
  apply nodeValid_prime [2, 7, 71, 557] ⟨1107317, 3, [(2, 2), (7, 1), (71, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_557
  · decide +kernel

theorem prime_1141541 : Nat.Prime 1141541 := by
  apply nodeValid_prime [2, 5, 57077] ⟨1141541, 3, [(2, 2), (5, 1), (57077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_57077
  · decide +kernel

theorem prime_1356743 : Nat.Prime 1356743 := by
  apply nodeValid_prime [2, 678371] ⟨1356743, 5, [(2, 1), (678371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_678371
  · decide +kernel

theorem prime_1402301 : Nat.Prime 1402301 := by
  apply nodeValid_prime [2, 5, 37, 379] ⟨1402301, 3, [(2, 2), (5, 2), (37, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_379
  · decide +kernel

theorem prime_1448779 : Nat.Prime 1448779 := by
  apply nodeValid_prime [2, 3, 241463] ⟨1448779, 3, [(2, 1), (3, 1), (241463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241463
  · decide +kernel

theorem prime_1567297 : Nat.Prime 1567297 := by
  apply nodeValid_prime [2, 3, 907] ⟨1567297, 10, [(2, 6), (3, 3), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
  · decide +kernel

theorem prime_2076929 : Nat.Prime 2076929 := by
  apply nodeValid_prime [2, 7, 19, 61] ⟨2076929, 3, [(2, 8), (7, 1), (19, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_2129177 : Nat.Prime 2129177 := by
  apply nodeValid_prime [2, 7, 193, 197] ⟨2129177, 3, [(2, 3), (7, 1), (193, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_193
    · exact prime_197
  · decide +kernel

theorem prime_2550659 : Nat.Prime 2550659 := by
  apply nodeValid_prime [2, 11, 269, 431] ⟨2550659, 2, [(2, 1), (11, 1), (269, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_269
    · exact prime_431
  · decide +kernel

theorem prime_3106021 : Nat.Prime 3106021 := by
  apply nodeValid_prime [2, 3, 5, 51767] ⟨3106021, 6, [(2, 2), (3, 1), (5, 1), (51767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_51767
  · decide +kernel

theorem prime_3564971 : Nat.Prime 3564971 := by
  apply nodeValid_prime [2, 5, 19, 29, 647] ⟨3564971, 2, [(2, 1), (5, 1), (19, 1), (29, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_647
  · decide +kernel

theorem prime_9052181 : Nat.Prime 9052181 := by
  apply nodeValid_prime [2, 5, 439, 1031] ⟨9052181, 2, [(2, 2), (5, 1), (439, 1), (1031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_439
    · exact prime_1031
  · decide +kernel

theorem prime_15450107 : Nat.Prime 15450107 := by
  apply nodeValid_prime [2, 7, 1103579] ⟨15450107, 2, [(2, 1), (7, 1), (1103579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1103579
  · decide +kernel

theorem prime_16340827 : Nat.Prime 16340827 := by
  apply nodeValid_prime [2, 3, 107, 25453] ⟨16340827, 2, [(2, 1), (3, 1), (107, 1), (25453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_25453
  · decide +kernel

theorem prime_16987123 : Nat.Prime 16987123 := by
  apply nodeValid_prime [2, 3, 943729] ⟨16987123, 3, [(2, 1), (3, 2), (943729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_943729
  · decide +kernel

theorem prime_19931707 : Nat.Prime 19931707 := by
  apply nodeValid_prime [2, 3, 1107317] ⟨19931707, 3, [(2, 1), (3, 2), (1107317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1107317
  · decide +kernel

theorem prime_21502301 : Nat.Prime 21502301 := by
  apply nodeValid_prime [2, 5, 19, 11317] ⟨21502301, 3, [(2, 2), (5, 2), (19, 1), (11317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_11317
  · decide +kernel

theorem prime_22583023 : Nat.Prime 22583023 := by
  apply nodeValid_prime [2, 3, 7, 11, 6983] ⟨22583023, 3, [(2, 1), (3, 1), (7, 2), (11, 1), (6983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_6983
  · decide +kernel

theorem prime_29808479 : Nat.Prime 29808479 := by
  apply nodeValid_prime [2, 7, 2129177] ⟨29808479, 14, [(2, 1), (7, 1), (2129177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2129177
  · decide +kernel

theorem prime_30458959 : Nat.Prime 30458959 := by
  apply nodeValid_prime [2, 3, 73, 197, 353] ⟨30458959, 6, [(2, 1), (3, 1), (73, 1), (197, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_197
    · exact prime_353
  · decide +kernel

theorem prime_37618369 : Nat.Prime 37618369 := by
  apply nodeValid_prime [2, 3, 195929] ⟨37618369, 7, [(2, 6), (3, 1), (195929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_195929
  · decide +kernel

theorem prime_40402643 : Nat.Prime 40402643 := by
  apply nodeValid_prime [2, 7, 17, 53, 3203] ⟨40402643, 5, [(2, 1), (7, 1), (17, 1), (53, 1), (3203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_53
    · exact prime_3203
  · decide +kernel

theorem prime_44260289 : Nat.Prime 44260289 := by
  apply nodeValid_prime [2, 37, 18691] ⟨44260289, 3, [(2, 6), (37, 1), (18691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_18691
  · decide +kernel

theorem prime_49328581 : Nat.Prime 49328581 := by
  apply nodeValid_prime [2, 3, 5, 7, 257, 457] ⟨49328581, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (257, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_257
    · exact prime_457
  · decide +kernel

theorem prime_64439407 : Nat.Prime 64439407 := by
  apply nodeValid_prime [2, 3, 389, 9203] ⟨64439407, 3, [(2, 1), (3, 2), (389, 1), (9203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_9203
  · decide +kernel

theorem prime_72964949 : Nat.Prime 72964949 := by
  apply nodeValid_prime [2, 7, 31, 84061] ⟨72964949, 2, [(2, 2), (7, 1), (31, 1), (84061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_84061
  · decide +kernel

theorem prime_93508711 : Nat.Prime 93508711 := by
  apply nodeValid_prime [2, 3, 5, 31, 100547] ⟨93508711, 3, [(2, 1), (3, 1), (5, 1), (31, 1), (100547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_100547
  · decide +kernel

theorem prime_122432239 : Nat.Prime 122432239 := by
  apply nodeValid_prime [2, 3, 19, 357989] ⟨122432239, 6, [(2, 1), (3, 2), (19, 1), (357989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_357989
  · decide +kernel

theorem prime_125512213 : Nat.Prime 125512213 := by
  apply nodeValid_prime [2, 3, 7, 191, 7823] ⟨125512213, 2, [(2, 2), (3, 1), (7, 1), (191, 1), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_191
    · exact prime_7823
  · decide +kernel

theorem prime_271793969 : Nat.Prime 271793969 := by
  apply nodeValid_prime [2, 16987123] ⟨271793969, 3, [(2, 4), (16987123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16987123
  · decide +kernel

theorem prime_279194533 : Nat.Prime 279194533 := by
  apply nodeValid_prime [2, 3, 79, 294509] ⟨279194533, 5, [(2, 2), (3, 1), (79, 1), (294509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_294509
  · decide +kernel

theorem prime_290775127 : Nat.Prime 290775127 := by
  apply nodeValid_prime [2, 3, 19, 2550659] ⟨290775127, 5, [(2, 1), (3, 1), (19, 1), (2550659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_2550659
  · decide +kernel

theorem prime_315561187 : Nat.Prime 315561187 := by
  apply nodeValid_prime [2, 3, 83, 211219] ⟨315561187, 5, [(2, 1), (3, 2), (83, 1), (211219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_211219
  · decide +kernel

theorem prime_417626689 : Nat.Prime 417626689 := by
  apply nodeValid_prime [2, 3, 19, 239, 479] ⟨417626689, 11, [(2, 6), (3, 1), (19, 1), (239, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_239
    · exact prime_479
  · decide +kernel

theorem prime_484831717 : Nat.Prime 484831717 := by
  apply nodeValid_prime [2, 3, 40402643] ⟨484831717, 2, [(2, 2), (3, 1), (40402643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40402643
  · decide +kernel

theorem prime_731784043 : Nat.Prime 731784043 := by
  apply nodeValid_prime [2, 3, 11, 337, 997] ⟨731784043, 2, [(2, 1), (3, 2), (11, 2), (337, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_337
    · exact prime_997
  · decide +kernel

theorem prime_1867300049 : Nat.Prime 1867300049 := by
  apply nodeValid_prime [2, 2917, 40009] ⟨1867300049, 3, [(2, 4), (2917, 1), (40009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2917
    · exact prime_40009
  · decide +kernel

theorem prime_2213014451 : Nat.Prime 2213014451 := by
  apply nodeValid_prime [2, 5, 44260289] ⟨2213014451, 2, [(2, 1), (5, 2), (44260289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_44260289
  · decide +kernel

theorem prime_2404148597 : Nat.Prime 2404148597 := by
  apply nodeValid_prime [2, 443, 1356743] ⟨2404148597, 2, [(2, 2), (443, 1), (1356743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_1356743
  · decide +kernel

theorem prime_2654730317 : Nat.Prime 2654730317 := by
  apply nodeValid_prime [2, 7, 37, 109, 23509] ⟨2654730317, 2, [(2, 2), (7, 1), (37, 1), (109, 1), (23509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_109
    · exact prime_23509
  · decide +kernel

theorem prime_3059360299 : Nat.Prime 3059360299 := by
  apply nodeValid_prime [2, 3, 67, 487, 5209] ⟨3059360299, 2, [(2, 1), (3, 2), (67, 1), (487, 1), (5209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_487
    · exact prime_5209
  · decide +kernel

theorem prime_3351653813 : Nat.Prime 3351653813 := by
  apply nodeValid_prime [2, 13, 863, 74687] ⟨3351653813, 2, [(2, 2), (13, 1), (863, 1), (74687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_863
    · exact prime_74687
  · decide +kernel

theorem prime_3734600099 : Nat.Prime 3734600099 := by
  apply nodeValid_prime [2, 1867300049] ⟨3734600099, 2, [(2, 1), (1867300049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1867300049
  · decide +kernel

theorem prime_3765366391 : Nat.Prime 3765366391 := by
  apply nodeValid_prime [2, 3, 5, 125512213] ⟨3765366391, 6, [(2, 1), (3, 1), (5, 1), (125512213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_125512213
  · decide +kernel

theorem prime_4234350509 : Nat.Prime 4234350509 := by
  apply nodeValid_prime [2, 23, 47, 89, 11003] ⟨4234350509, 2, [(2, 2), (23, 1), (47, 1), (89, 1), (11003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_89
    · exact prime_11003
  · decide +kernel

theorem prime_6833139343 : Nat.Prime 6833139343 := by
  apply nodeValid_prime [2, 3, 1321, 862117] ⟨6833139343, 5, [(2, 1), (3, 1), (1321, 1), (862117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1321
    · exact prime_862117
  · decide +kernel

theorem prime_7469200199 : Nat.Prime 7469200199 := by
  apply nodeValid_prime [2, 3734600099] ⟨7469200199, 13, [(2, 1), (3734600099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3734600099
  · decide +kernel

theorem prime_13771236439 : Nat.Prime 13771236439 := by
  apply nodeValid_prime [2, 3, 29, 137, 64189] ⟨13771236439, 3, [(2, 1), (3, 3), (29, 1), (137, 1), (64189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_137
    · exact prime_64189
  · decide +kernel

theorem prime_17540320939 : Nat.Prime 17540320939 := by
  apply nodeValid_prime [2, 3, 7, 417626689] ⟨17540320939, 2, [(2, 1), (3, 1), (7, 1), (417626689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_417626689
  · decide +kernel

theorem prime_88264985873 : Nat.Prime 88264985873 := by
  apply nodeValid_prime [2, 7, 2663, 295937] ⟨88264985873, 3, [(2, 4), (7, 1), (2663, 1), (295937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2663
    · exact prime_295937
  · decide +kernel

theorem prime_132736515851 : Nat.Prime 132736515851 := by
  apply nodeValid_prime [2, 5, 2654730317] ⟨132736515851, 2, [(2, 1), (5, 2), (2654730317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2654730317
  · decide +kernel

theorem prime_174505330451 : Nat.Prime 174505330451 := by
  apply nodeValid_prime [2, 5, 11, 89, 3564971] ⟨174505330451, 2, [(2, 1), (5, 2), (11, 1), (89, 1), (3564971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_89
    · exact prime_3564971
  · decide +kernel

theorem prime_174505336417 : Nat.Prime 174505336417 := by
  apply nodeValid_prime [2, 3, 1889, 106921] ⟨174505336417, 5, [(2, 5), (3, 3), (1889, 1), (106921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1889
    · exact prime_106921
  · decide +kernel

theorem prime_175628170321 : Nat.Prime 175628170321 := by
  apply nodeValid_prime [2, 3, 5, 731784043] ⟨175628170321, 19, [(2, 4), (3, 1), (5, 1), (731784043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_731784043
  · decide +kernel

theorem prime_266492428513 : Nat.Prime 266492428513 := by
  apply nodeValid_prime [2, 3, 31, 227, 394481] ⟨266492428513, 5, [(2, 5), (3, 1), (31, 1), (227, 1), (394481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_227
    · exact prime_394481
  · decide +kernel

theorem prime_524861640623 : Nat.Prime 524861640623 := by
  apply nodeValid_prime [2, 11, 7681, 3106021] ⟨524861640623, 5, [(2, 1), (11, 1), (7681, 1), (3106021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_7681
    · exact prime_3106021
  · decide +kernel

theorem prime_537762512909 : Nat.Prime 537762512909 := by
  apply nodeValid_prime [2, 128483, 1046369] ⟨537762512909, 2, [(2, 2), (128483, 1), (1046369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_128483
    · exact prime_1046369
  · decide +kernel

theorem prime_1045688024791 : Nat.Prime 1045688024791 := by
  apply nodeValid_prime [2, 3, 5, 23, 859, 588083] ⟨1045688024791, 3, [(2, 1), (3, 2), (5, 1), (23, 1), (859, 1), (588083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_859
    · exact prime_588083
  · decide +kernel

theorem prime_1045688027861 : Nat.Prime 1045688027861 := by
  apply nodeValid_prime [2, 5, 7, 7469200199] ⟨1045688027861, 3, [(2, 2), (5, 1), (7, 1), (7469200199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7469200199
  · decide +kernel

theorem prime_1045688085313 : Nat.Prime 1045688085313 := by
  apply nodeValid_prime [2, 3, 13, 367, 1141541] ⟨1045688085313, 10, [(2, 6), (3, 1), (13, 1), (367, 1), (1141541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_367
    · exact prime_1141541
  · decide +kernel

theorem prime_1047031982707 : Nat.Prime 1047031982707 := by
  apply nodeValid_prime [2, 3, 174505330451] ⟨1047031982707, 2, [(2, 1), (3, 1), (174505330451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_174505330451
  · decide +kernel

theorem prime_1047032018467 : Nat.Prime 1047032018467 := by
  apply nodeValid_prime [2, 3, 7, 79, 315561187] ⟨1047032018467, 2, [(2, 1), (3, 1), (7, 1), (79, 1), (315561187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_315561187
  · decide +kernel

theorem prime_1047032018503 : Nat.Prime 1047032018503 := by
  apply nodeValid_prime [2, 3, 174505336417] ⟨1047032018503, 5, [(2, 1), (3, 1), (174505336417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_174505336417
  · decide +kernel

theorem prime_1048377055213 : Nat.Prime 1048377055213 := by
  apply nodeValid_prime [2, 3, 19, 1093, 1402301] ⟨1048377055213, 6, [(2, 2), (3, 2), (19, 1), (1093, 1), (1402301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1093
    · exact prime_1402301
  · decide +kernel

theorem prime_1048377067273 : Nat.Prime 1048377067273 := by
  apply nodeValid_prime [2, 3, 28097, 518233] ⟨1048377067273, 5, [(2, 3), (3, 2), (28097, 1), (518233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28097
    · exact prime_518233
  · decide +kernel

theorem prime_1048377067721 : Nat.Prime 1048377067721 := by
  apply nodeValid_prime [2, 5, 23, 43, 2137, 12401] ⟨1048377067721, 3, [(2, 3), (5, 1), (23, 1), (43, 1), (2137, 1), (12401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_43
    · exact prime_2137
    · exact prime_12401
  · decide +kernel

theorem prime_1049723280863 : Nat.Prime 1049723280863 := by
  apply nodeValid_prime [2, 17, 1549, 19931707] ⟨1049723280863, 10, [(2, 1), (17, 1), (1549, 1), (19931707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1549
    · exact prime_19931707
  · decide +kernel

theorem prime_1049723281247 : Nat.Prime 1049723281247 := by
  apply nodeValid_prime [2, 524861640623] ⟨1049723281247, 5, [(2, 1), (524861640623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_524861640623
  · decide +kernel

theorem prime_1049723295157 : Nat.Prime 1049723295157 := by
  apply nodeValid_prime [2, 3, 67, 2777, 156719] ⟨1049723295157, 2, [(2, 2), (3, 2), (67, 1), (2777, 1), (156719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_2777
    · exact prime_156719
  · decide +kernel

theorem prime_1051070706661 : Nat.Prime 1051070706661 := by
  apply nodeValid_prime [2, 3, 5, 13, 59, 101, 226133] ⟨1051070706661, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (59, 1), (101, 1), (226133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_59
    · exact prime_101
    · exact prime_226133
  · decide +kernel

theorem prime_1051070777423 : Nat.Prime 1051070777423 := by
  apply nodeValid_prime [2, 311, 28283, 59747] ⟨1051070777423, 5, [(2, 1), (311, 1), (28283, 1), (59747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_28283
    · exact prime_59747
  · decide +kernel

theorem prime_1051070779211 : Nat.Prime 1051070779211 := by
  apply nodeValid_prime [2, 5, 6803, 15450107] ⟨1051070779211, 2, [(2, 1), (5, 1), (6803, 1), (15450107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6803
    · exact prime_15450107
  · decide +kernel

theorem prime_1052419255691 : Nat.Prime 1052419255691 := by
  apply nodeValid_prime [2, 5, 11, 11657, 820747] ⟨1052419255691, 2, [(2, 1), (5, 1), (11, 1), (11657, 1), (820747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_11657
    · exact prime_820747
  · decide +kernel

theorem prime_1052419256341 : Nat.Prime 1052419256341 := by
  apply nodeValid_prime [2, 3, 5, 17540320939] ⟨1052419256341, 11, [(2, 2), (3, 1), (5, 1), (17540320939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17540320939
  · decide +kernel

theorem prime_1052419297283 : Nat.Prime 1052419297283 := by
  apply nodeValid_prime [2, 157, 3351653813] ⟨1052419297283, 2, [(2, 1), (157, 1), (3351653813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_3351653813
  · decide +kernel

theorem prime_1053769019227 : Nat.Prime 1053769019227 := by
  apply nodeValid_prime [2, 3, 7, 11, 101, 22583023] ⟨1053769019227, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (101, 1), (22583023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_101
    · exact prime_22583023
  · decide +kernel

theorem prime_1053769021927 : Nat.Prime 1053769021927 := by
  apply nodeValid_prime [2, 3, 175628170321] ⟨1053769021927, 5, [(2, 1), (3, 1), (175628170321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_175628170321
  · decide +kernel

theorem prime_1053769060249 : Nat.Prime 1053769060249 := by
  apply nodeValid_prime [2, 3, 151, 290775127] ⟨1053769060249, 7, [(2, 3), (3, 1), (151, 1), (290775127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_290775127
  · decide +kernel

theorem prime_1055119998271 : Nat.Prime 1055119998271 := by
  apply nodeValid_prime [2, 3, 5, 13, 37, 179, 408491] ⟨1055119998271, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (37, 1), (179, 1), (408491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_179
    · exact prime_408491
  · decide +kernel

theorem prime_1055120013371 : Nat.Prime 1055120013371 := by
  apply nodeValid_prime [2, 5, 23, 2927, 1567297] ⟨1055120013371, 2, [(2, 1), (5, 1), (23, 1), (2927, 1), (1567297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_2927
    · exact prime_1567297
  · decide +kernel

theorem prime_1055120013713 : Nat.Prime 1055120013713 := by
  apply nodeValid_prime [2, 1753, 37618369] ⟨1055120013713, 3, [(2, 4), (1753, 1), (37618369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1753
    · exact prime_37618369
  · decide +kernel

theorem prime_1056472102643 : Nat.Prime 1056472102643 := by
  apply nodeValid_prime [2, 11, 18443, 236707] ⟨1056472102643, 6, [(2, 1), (11, 2), (18443, 1), (236707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_18443
    · exact prime_236707
  · decide +kernel

theorem prime_1056472112719 : Nat.Prime 1056472112719 := by
  apply nodeValid_prime [2, 3, 11, 179, 29808479] ⟨1056472112719, 3, [(2, 1), (3, 2), (11, 1), (179, 1), (29808479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_179
    · exact prime_29808479
  · decide +kernel

theorem prime_1056472112873 : Nat.Prime 1056472112873 := by
  apply nodeValid_prime [2, 11, 43, 279194533] ⟨1056472112873, 3, [(2, 3), (11, 1), (43, 1), (279194533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_279194533
  · decide +kernel

theorem prime_1057825381807 : Nat.Prime 1057825381807 := by
  apply nodeValid_prime [2, 3, 181, 787, 412561] ⟨1057825381807, 3, [(2, 1), (3, 2), (181, 1), (787, 1), (412561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_787
    · exact prime_412561
  · decide +kernel

theorem prime_1057825382171 : Nat.Prime 1057825382171 := by
  apply nodeValid_prime [2, 5, 227, 1279, 364349] ⟨1057825382171, 2, [(2, 1), (5, 1), (227, 1), (1279, 1), (364349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
    · exact prime_1279
    · exact prime_364349
  · decide +kernel

theorem prime_1057825382681 : Nat.Prime 1057825382681 := by
  apply nodeValid_prime [2, 5, 11, 2404148597] ⟨1057825382681, 6, [(2, 3), (5, 1), (11, 1), (2404148597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2404148597
  · decide +kernel

theorem prime_1059179830469 : Nat.Prime 1059179830469 := by
  apply nodeValid_prime [2, 113, 2797, 837797] ⟨1059179830469, 2, [(2, 2), (113, 1), (2797, 1), (837797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_2797
    · exact prime_837797
  · decide +kernel

theorem prime_1059179830477 : Nat.Prime 1059179830477 := by
  apply nodeValid_prime [2, 3, 88264985873] ⟨1059179830477, 2, [(2, 2), (3, 1), (88264985873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_88264985873
  · decide +kernel

theorem prime_1059179840267 : Nat.Prime 1059179840267 := by
  apply nodeValid_prime [2, 17387, 30458959] ⟨1059179840267, 2, [(2, 1), (17387, 1), (30458959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17387
    · exact prime_30458959
  · decide +kernel

theorem prime_1060535421511 : Nat.Prime 1060535421511 := by
  apply nodeValid_prime [2, 3, 5, 153259, 230663] ⟨1060535421511, 11, [(2, 1), (3, 1), (5, 1), (153259, 1), (230663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_153259
    · exact prime_230663
  · decide +kernel

theorem prime_1060535421599 : Nat.Prime 1060535421599 := by
  apply nodeValid_prime [2, 58579, 9052181] ⟨1060535421599, 11, [(2, 1), (58579, 1), (9052181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_58579
    · exact prime_9052181
  · decide +kernel

theorem prime_1060535464147 : Nat.Prime 1060535464147 := by
  apply nodeValid_prime [2, 3, 131, 1559, 288493] ⟨1060535464147, 5, [(2, 1), (3, 2), (131, 1), (1559, 1), (288493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_1559
    · exact prime_288493
  · decide +kernel

theorem prime_1061892126809 : Nat.Prime 1061892126809 := by
  apply nodeValid_prime [2, 132736515851] ⟨1061892126809, 3, [(2, 3), (132736515851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_132736515851
  · decide +kernel

theorem prime_1061892127469 : Nat.Prime 1061892127469 := by
  apply nodeValid_prime [2, 59, 157, 4673, 6133] ⟨1061892127469, 2, [(2, 2), (59, 1), (157, 1), (4673, 1), (6133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_157
    · exact prime_4673
    · exact prime_6133
  · decide +kernel

theorem prime_1061892259121 : Nat.Prime 1061892259121 := by
  apply nodeValid_prime [2, 5, 7, 11, 83, 2076929] ⟨1061892259121, 3, [(2, 4), (5, 1), (7, 1), (11, 1), (83, 1), (2076929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_83
    · exact prime_2076929
  · decide +kernel

theorem prime_1063250215427 : Nat.Prime 1063250215427 := by
  apply nodeValid_prime [2, 7, 19, 31, 89, 1448779] ⟨1063250215427, 2, [(2, 1), (7, 1), (19, 1), (31, 1), (89, 1), (1448779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_31
    · exact prime_89
    · exact prime_1448779
  · decide +kernel

theorem prime_1063250215501 : Nat.Prime 1063250215501 := by
  apply nodeValid_prime [2, 3, 5, 11, 64439407] ⟨1063250215501, 2, [(2, 2), (3, 1), (5, 3), (11, 1), (64439407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_64439407
  · decide +kernel

theorem prime_1063250230969 : Nat.Prime 1063250230969 := by
  apply nodeValid_prime [2, 3, 19, 11057, 23431] ⟨1063250230969, 7, [(2, 3), (3, 3), (19, 1), (11057, 1), (23431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_11057
    · exact prime_23431
  · decide +kernel

theorem prime_1064609384149 : Nat.Prime 1064609384149 := by
  apply nodeValid_prime [2, 3, 44279, 667867] ⟨1064609384149, 2, [(2, 2), (3, 2), (44279, 1), (667867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44279
    · exact prime_667867
  · decide +kernel

theorem prime_1064609435041 : Nat.Prime 1064609435041 := by
  apply nodeValid_prime [2, 3, 5, 31, 4651, 15383] ⟨1064609435041, 14, [(2, 5), (3, 1), (5, 1), (31, 1), (4651, 1), (15383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_4651
    · exact prime_15383
  · decide +kernel

theorem prime_1064609435143 : Nat.Prime 1064609435143 := by
  apply nodeValid_prime [2, 3, 11, 109, 49328581] ⟨1064609435143, 3, [(2, 1), (3, 2), (11, 1), (109, 1), (49328581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_109
    · exact prime_49328581
  · decide +kernel

theorem prime_1065969714053 : Nat.Prime 1065969714053 := by
  apply nodeValid_prime [2, 266492428513] ⟨1065969714053, 2, [(2, 2), (266492428513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_266492428513
  · decide +kernel

theorem prime_1065969737509 : Nat.Prime 1065969737509 := by
  apply nodeValid_prime [2, 3, 13, 6833139343] ⟨1065969737509, 2, [(2, 2), (3, 1), (13, 1), (6833139343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6833139343
  · decide +kernel

theorem prime_1065969738919 : Nat.Prime 1065969738919 := by
  apply nodeValid_prime [2, 3, 7, 137, 509, 121321] ⟨1065969738919, 3, [(2, 1), (3, 2), (7, 1), (137, 1), (509, 1), (121321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_509
    · exact prime_121321
  · decide +kernel

theorem prime_1067331217039 : Nat.Prime 1067331217039 := by
  apply nodeValid_prime [2, 3, 8273, 21502301] ⟨1067331217039, 15, [(2, 1), (3, 1), (8273, 1), (21502301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8273
    · exact prime_21502301
  · decide +kernel

theorem prime_1067331271441 : Nat.Prime 1067331271441 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 191, 89899] ⟨1067331271441, 17, [(2, 4), (3, 1), (5, 1), (7, 1), (37, 1), (191, 1), (89899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_191
    · exact prime_89899
  · decide +kernel

theorem prime_1067331273973 : Nat.Prime 1067331273973 := by
  apply nodeValid_prime [2, 3, 23, 53, 72964949] ⟨1067331273973, 2, [(2, 2), (3, 1), (23, 1), (53, 1), (72964949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_53
    · exact prime_72964949
  · decide +kernel

theorem prime_1068693886109 : Nat.Prime 1068693886109 := by
  apply nodeValid_prime [2, 983, 271793969] ⟨1068693886109, 2, [(2, 2), (983, 1), (271793969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_983
    · exact prime_271793969
  · decide +kernel

theorem prime_1068693886121 : Nat.Prime 1068693886121 := by
  apply nodeValid_prime [2, 5, 7, 39113, 97583] ⟨1068693886121, 3, [(2, 3), (5, 1), (7, 1), (39113, 1), (97583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_39113
    · exact prime_97583
  · decide +kernel

theorem prime_1068693901789 : Nat.Prime 1068693901789 := by
  apply nodeValid_prime [2, 3, 17, 12823, 408539] ⟨1068693901789, 2, [(2, 2), (3, 1), (17, 1), (12823, 1), (408539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_12823
    · exact prime_408539
  · decide +kernel

theorem prime_1070057768497 : Nat.Prime 1070057768497 := by
  apply nodeValid_prime [2, 3, 71, 6871, 45697] ⟨1070057768497, 5, [(2, 4), (3, 1), (71, 1), (6871, 1), (45697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_6871
    · exact prime_45697
  · decide +kernel

theorem prime_1070057768861 : Nat.Prime 1070057768861 := by
  apply nodeValid_prime [2, 5, 19, 23, 122432239] ⟨1070057768861, 2, [(2, 2), (5, 1), (19, 1), (23, 1), (122432239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_122432239
  · decide +kernel

theorem prime_1070057771609 : Nat.Prime 1070057771609 := by
  apply nodeValid_prime [2, 7, 43, 1439, 308809] ⟨1070057771609, 6, [(2, 3), (7, 1), (43, 1), (1439, 1), (308809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_1439
    · exact prime_308809
  · decide +kernel

theorem prime_1071422810459 : Nat.Prime 1071422810459 := by
  apply nodeValid_prime [2, 7, 11, 13, 107, 714521] ⟨1071422810459, 2, [(2, 1), (7, 2), (11, 1), (13, 1), (107, 1), (714521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_107
    · exact prime_714521
  · decide +kernel

theorem prime_1071422810639 : Nat.Prime 1071422810639 := by
  apply nodeValid_prime [2, 17, 337, 93508711] ⟨1071422810639, 11, [(2, 1), (17, 1), (337, 1), (93508711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_337
    · exact prime_93508711
  · decide +kernel

theorem prime_1071422818139 : Nat.Prime 1071422818139 := by
  apply nodeValid_prime [2, 59, 73, 199, 625033] ⟨1071422818139, 2, [(2, 1), (59, 1), (73, 1), (199, 1), (625033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_73
    · exact prime_199
    · exact prime_625033
  · decide +kernel

theorem prime_1072789042279 : Nat.Prime 1072789042279 := by
  apply nodeValid_prime [2, 3, 31, 461, 2069, 6047] ⟨1072789042279, 6, [(2, 1), (3, 1), (31, 1), (461, 1), (2069, 1), (6047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_461
    · exact prime_2069
    · exact prime_6047
  · decide +kernel

theorem prime_1072789157749 : Nat.Prime 1072789157749 := by
  apply nodeValid_prime [2, 3, 7, 11, 103, 1093, 10313] ⟨1072789157749, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (103, 1), (1093, 1), (10313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_103
    · exact prime_1093
    · exact prime_10313
  · decide +kernel

theorem prime_1072789159027 : Nat.Prime 1072789159027 := by
  apply nodeValid_prime [2, 3, 13, 971, 2503, 5659] ⟨1072789159027, 2, [(2, 1), (3, 1), (13, 1), (971, 1), (2503, 1), (5659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_971
    · exact prime_2503
    · exact prime_5659
  · decide +kernel

theorem prime_1074156442243 : Nat.Prime 1074156442243 := by
  apply nodeValid_prime [2, 3, 13, 13771236439] ⟨1074156442243, 14, [(2, 1), (3, 1), (13, 1), (13771236439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_13771236439
  · decide +kernel

theorem prime_1074156467981 : Nat.Prime 1074156467981 := by
  apply nodeValid_prime [2, 5, 241, 1567, 142217] ⟨1074156467981, 2, [(2, 2), (5, 1), (241, 1), (1567, 1), (142217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_241
    · exact prime_1567
    · exact prime_142217
  · decide +kernel

theorem prime_1074156472019 : Nat.Prime 1074156472019 := by
  apply nodeValid_prime [2, 7, 223, 379, 907811] ⟨1074156472019, 2, [(2, 1), (7, 1), (223, 1), (379, 1), (907811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_223
    · exact prime_379
    · exact prime_907811
  · decide +kernel

theorem prime_1075525023187 : Nat.Prime 1075525023187 := by
  apply nodeValid_prime [2, 3, 2213014451] ⟨1075525023187, 2, [(2, 1), (3, 5), (2213014451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2213014451
  · decide +kernel

theorem prime_1075525025819 : Nat.Prime 1075525025819 := by
  apply nodeValid_prime [2, 537762512909] ⟨1075525025819, 2, [(2, 1), (537762512909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_537762512909
  · decide +kernel

theorem prime_1075525029287 : Nat.Prime 1075525029287 := by
  apply nodeValid_prime [2, 127, 4234350509] ⟨1075525029287, 5, [(2, 1), (127, 1), (4234350509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_4234350509
  · decide +kernel

theorem prime_1076894787827 : Nat.Prime 1076894787827 := by
  apply nodeValid_prime [2, 11, 13, 3765366391] ⟨1076894787827, 2, [(2, 1), (11, 1), (13, 1), (3765366391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_3765366391
  · decide +kernel

theorem prime_1076894824861 : Nat.Prime 1076894824861 := by
  apply nodeValid_prime [2, 3, 5, 19717, 303431] ⟨1076894824861, 6, [(2, 2), (3, 2), (5, 1), (19717, 1), (303431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19717
    · exact prime_303431
  · decide +kernel

theorem prime_1076894825249 : Nat.Prime 1076894825249 := by
  apply nodeValid_prime [2, 11, 3059360299] ⟨1076894825249, 3, [(2, 5), (11, 1), (3059360299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3059360299
  · decide +kernel

theorem prime_1078265738609 : Nat.Prime 1078265738609 := by
  apply nodeValid_prime [2, 139, 484831717] ⟨1078265738609, 3, [(2, 4), (139, 1), (484831717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_484831717
  · decide +kernel

theorem prime_1078265810423 : Nat.Prime 1078265810423 := by
  apply nodeValid_prime [2, 32993, 16340827] ⟨1078265810423, 5, [(2, 1), (32993, 1), (16340827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32993
    · exact prime_16340827
  · decide +kernel

theorem prime_1078265810701 : Nat.Prime 1078265810701 := by
  apply nodeValid_prime [2, 3, 5, 13, 61, 157, 9623] ⟨1078265810701, 2, [(2, 2), (3, 2), (5, 2), (13, 1), (61, 1), (157, 1), (9623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_61
    · exact prime_157
    · exact prime_9623
  · decide +kernel

end Sude.Lucas.Generated
