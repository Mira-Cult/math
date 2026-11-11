import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4463 : Nat.Prime 4463 := by
  apply nodeValid_prime [2, 23, 97] ⟨4463, 5, [(2, 1), (23, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_97
  · decide +kernel

theorem prime_5519 : Nat.Prime 5519 := by
  apply nodeValid_prime [2, 31, 89] ⟨5519, 13, [(2, 1), (31, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_89
  · decide +kernel

theorem prime_5857 : Nat.Prime 5857 := by
  apply nodeValid_prime [2, 3, 61] ⟨5857, 7, [(2, 5), (3, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel

theorem prime_6991 : Nat.Prime 6991 := by
  apply nodeValid_prime [2, 3, 5, 233] ⟨6991, 6, [(2, 1), (3, 1), (5, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_233
  · decide +kernel

theorem prime_7253 : Nat.Prime 7253 := by
  apply nodeValid_prime [2, 7, 37] ⟨7253, 2, [(2, 2), (7, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_7687 : Nat.Prime 7687 := by
  apply nodeValid_prime [2, 3, 7, 61] ⟨7687, 6, [(2, 1), (3, 2), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_7879 : Nat.Prime 7879 := by
  apply nodeValid_prime [2, 3, 13, 101] ⟨7879, 3, [(2, 1), (3, 1), (13, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
  · decide +kernel

theorem prime_8273 : Nat.Prime 8273 := by
  apply nodeValid_prime [2, 11, 47] ⟨8273, 3, [(2, 4), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_8951 : Nat.Prime 8951 := by
  apply nodeValid_prime [2, 5, 179] ⟨8951, 13, [(2, 1), (5, 2), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_179
  · decide +kernel

theorem prime_9091 : Nat.Prime 9091 := by
  apply nodeValid_prime [2, 3, 5, 101] ⟨9091, 3, [(2, 1), (3, 2), (5, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
  · decide +kernel

theorem prime_9391 : Nat.Prime 9391 := by
  apply nodeValid_prime [2, 3, 5, 313] ⟨9391, 3, [(2, 1), (3, 1), (5, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_313
  · decide +kernel

theorem prime_11059 : Nat.Prime 11059 := by
  apply nodeValid_prime [2, 3, 19, 97] ⟨11059, 10, [(2, 1), (3, 1), (19, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_97
  · decide +kernel

theorem prime_12601 : Nat.Prime 12601 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨12601, 11, [(2, 3), (3, 2), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_13297 : Nat.Prime 13297 := by
  apply nodeValid_prime [2, 3, 277] ⟨13297, 5, [(2, 4), (3, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
  · decide +kernel

theorem prime_13729 : Nat.Prime 13729 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨13729, 23, [(2, 5), (3, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_13913 : Nat.Prime 13913 := by
  apply nodeValid_prime [2, 37, 47] ⟨13913, 3, [(2, 3), (37, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_47
  · decide +kernel

theorem prime_16139 : Nat.Prime 16139 := by
  apply nodeValid_prime [2, 8069] ⟨16139, 2, [(2, 1), (8069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8069
  · decide +kernel

theorem prime_16691 : Nat.Prime 16691 := by
  apply nodeValid_prime [2, 5, 1669] ⟨16691, 6, [(2, 1), (5, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1669
  · decide +kernel

theorem prime_17783 : Nat.Prime 17783 := by
  apply nodeValid_prime [2, 17, 523] ⟨17783, 5, [(2, 1), (17, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_523
  · decide +kernel

theorem prime_20807 : Nat.Prime 20807 := by
  apply nodeValid_prime [2, 101, 103] ⟨20807, 5, [(2, 1), (101, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_103
  · decide +kernel

theorem prime_21737 : Nat.Prime 21737 := by
  apply nodeValid_prime [2, 11, 13, 19] ⟨21737, 6, [(2, 3), (11, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_22153 : Nat.Prime 22153 := by
  apply nodeValid_prime [2, 3, 13, 71] ⟨22153, 5, [(2, 3), (3, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_25117 : Nat.Prime 25117 := by
  apply nodeValid_prime [2, 3, 7, 13, 23] ⟨25117, 5, [(2, 2), (3, 1), (7, 1), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_25307 : Nat.Prime 25307 := by
  apply nodeValid_prime [2, 12653] ⟨25307, 2, [(2, 1), (12653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12653
  · decide +kernel

theorem prime_27827 : Nat.Prime 27827 := by
  apply nodeValid_prime [2, 13913] ⟨27827, 2, [(2, 1), (13913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13913
  · decide +kernel

theorem prime_28387 : Nat.Prime 28387 := by
  apply nodeValid_prime [2, 3, 19, 83] ⟨28387, 2, [(2, 1), (3, 2), (19, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_83
  · decide +kernel

theorem prime_30109 : Nat.Prime 30109 := by
  apply nodeValid_prime [2, 3, 13, 193] ⟨30109, 2, [(2, 2), (3, 1), (13, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_193
  · decide +kernel

theorem prime_31271 : Nat.Prime 31271 := by
  apply nodeValid_prime [2, 5, 53, 59] ⟨31271, 7, [(2, 1), (5, 1), (53, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_59
  · decide +kernel

theorem prime_38053 : Nat.Prime 38053 := by
  apply nodeValid_prime [2, 3, 7, 151] ⟨38053, 5, [(2, 2), (3, 2), (7, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
  · decide +kernel

theorem prime_39161 : Nat.Prime 39161 := by
  apply nodeValid_prime [2, 5, 11, 89] ⟨39161, 3, [(2, 3), (5, 1), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_40847 : Nat.Prime 40847 := by
  apply nodeValid_prime [2, 13, 1571] ⟨40847, 5, [(2, 1), (13, 1), (1571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1571
  · decide +kernel

theorem prime_42491 : Nat.Prime 42491 := by
  apply nodeValid_prime [2, 5, 7, 607] ⟨42491, 2, [(2, 1), (5, 1), (7, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_607
  · decide +kernel

theorem prime_51071 : Nat.Prime 51071 := by
  apply nodeValid_prime [2, 5, 5107] ⟨51071, 11, [(2, 1), (5, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5107
  · decide +kernel

theorem prime_54547 : Nat.Prime 54547 := by
  apply nodeValid_prime [2, 3, 9091] ⟨54547, 3, [(2, 1), (3, 1), (9091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9091
  · decide +kernel

theorem prime_55213 : Nat.Prime 55213 := by
  apply nodeValid_prime [2, 3, 43, 107] ⟨55213, 2, [(2, 2), (3, 1), (43, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_107
  · decide +kernel

theorem prime_66037 : Nat.Prime 66037 := by
  apply nodeValid_prime [2, 3, 5503] ⟨66037, 2, [(2, 2), (3, 1), (5503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5503
  · decide +kernel

theorem prime_69911 : Nat.Prime 69911 := by
  apply nodeValid_prime [2, 5, 6991] ⟨69911, 7, [(2, 1), (5, 1), (6991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6991
  · decide +kernel

theorem prime_87037 : Nat.Prime 87037 := by
  apply nodeValid_prime [2, 3, 7253] ⟨87037, 2, [(2, 2), (3, 1), (7253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7253
  · decide +kernel

theorem prime_100469 : Nat.Prime 100469 := by
  apply nodeValid_prime [2, 25117] ⟨100469, 2, [(2, 2), (25117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25117
  · decide +kernel

theorem prime_101009 : Nat.Prime 101009 := by
  apply nodeValid_prime [2, 59, 107] ⟨101009, 3, [(2, 4), (59, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_107
  · decide +kernel

theorem prime_108499 : Nat.Prime 108499 := by
  apply nodeValid_prime [2, 3, 13, 107] ⟨108499, 14, [(2, 1), (3, 1), (13, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_107
  · decide +kernel

theorem prime_108769 : Nat.Prime 108769 := by
  apply nodeValid_prime [2, 3, 11, 103] ⟨108769, 7, [(2, 5), (3, 1), (11, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_103
  · decide +kernel

theorem prime_110119 : Nat.Prime 110119 := by
  apply nodeValid_prime [2, 3, 18353] ⟨110119, 3, [(2, 1), (3, 1), (18353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18353
  · decide +kernel

theorem prime_114143 : Nat.Prime 114143 := by
  apply nodeValid_prime [2, 7, 31, 263] ⟨114143, 5, [(2, 1), (7, 1), (31, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_263
  · decide +kernel

theorem prime_149351 : Nat.Prime 149351 := by
  apply nodeValid_prime [2, 5, 29, 103] ⟨149351, 11, [(2, 1), (5, 2), (29, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_103
  · decide +kernel

theorem prime_152459 : Nat.Prime 152459 := by
  apply nodeValid_prime [2, 31, 2459] ⟨152459, 2, [(2, 1), (31, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2459
  · decide +kernel

theorem prime_155773 : Nat.Prime 155773 := by
  apply nodeValid_prime [2, 3, 4327] ⟨155773, 5, [(2, 2), (3, 2), (4327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4327
  · decide +kernel

theorem prime_174263 : Nat.Prime 174263 := by
  apply nodeValid_prime [2, 11, 89] ⟨174263, 5, [(2, 1), (11, 1), (89, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_204749 : Nat.Prime 204749 := by
  apply nodeValid_prime [2, 17, 3011] ⟨204749, 2, [(2, 2), (17, 1), (3011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3011
  · decide +kernel

theorem prime_209959 : Nat.Prime 209959 := by
  apply nodeValid_prime [2, 3, 7, 4999] ⟨209959, 3, [(2, 1), (3, 1), (7, 1), (4999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4999
  · decide +kernel

theorem prime_269651 : Nat.Prime 269651 := by
  apply nodeValid_prime [2, 5, 5393] ⟨269651, 2, [(2, 1), (5, 2), (5393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5393
  · decide +kernel

theorem prime_277223 : Nat.Prime 277223 := by
  apply nodeValid_prime [2, 11, 12601] ⟨277223, 5, [(2, 1), (11, 1), (12601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12601
  · decide +kernel

theorem prime_303469 : Nat.Prime 303469 := by
  apply nodeValid_prime [2, 3, 11, 19] ⟨303469, 2, [(2, 2), (3, 1), (11, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_342179 : Nat.Prime 342179 := by
  apply nodeValid_prime [2, 31, 5519] ⟨342179, 2, [(2, 1), (31, 1), (5519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_5519
  · decide +kernel

theorem prime_365003 : Nat.Prime 365003 := by
  apply nodeValid_prime [2, 11, 47, 353] ⟨365003, 2, [(2, 1), (11, 1), (47, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_353
  · decide +kernel

theorem prime_409499 : Nat.Prime 409499 := by
  apply nodeValid_prime [2, 204749] ⟨409499, 2, [(2, 1), (204749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_204749
  · decide +kernel

theorem prime_534631 : Nat.Prime 534631 := by
  apply nodeValid_prime [2, 3, 5, 71, 251] ⟨534631, 6, [(2, 1), (3, 1), (5, 1), (71, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
    · exact prime_251
  · decide +kernel

theorem prime_612853 : Nat.Prime 612853 := by
  apply nodeValid_prime [2, 3, 51071] ⟨612853, 2, [(2, 2), (3, 1), (51071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51071
  · decide +kernel

theorem prime_716249 : Nat.Prime 716249 := by
  apply nodeValid_prime [2, 13, 71, 97] ⟨716249, 3, [(2, 3), (13, 1), (71, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71
    · exact prime_97
  · decide +kernel

theorem prime_816941 : Nat.Prime 816941 := by
  apply nodeValid_prime [2, 5, 40847] ⟨816941, 2, [(2, 2), (5, 1), (40847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40847
  · decide +kernel

theorem prime_941441 : Nat.Prime 941441 := by
  apply nodeValid_prime [2, 5, 1471] ⟨941441, 3, [(2, 7), (5, 1), (1471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1471
  · decide +kernel

theorem prime_988489 : Nat.Prime 988489 := by
  apply nodeValid_prime [2, 3, 13729] ⟨988489, 7, [(2, 3), (3, 2), (13729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13729
  · decide +kernel

theorem prime_1242169 : Nat.Prime 1242169 := by
  apply nodeValid_prime [2, 3, 73, 709] ⟨1242169, 13, [(2, 3), (3, 1), (73, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_709
  · decide +kernel

theorem prime_1249151 : Nat.Prime 1249151 := by
  apply nodeValid_prime [2, 5, 7, 43, 83] ⟨1249151, 7, [(2, 1), (5, 2), (7, 1), (43, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_83
  · decide +kernel

theorem prime_1288541 : Nat.Prime 1288541 := by
  apply nodeValid_prime [2, 5, 11, 5857] ⟨1288541, 2, [(2, 2), (5, 1), (11, 1), (5857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_5857
  · decide +kernel

theorem prime_1344601 : Nat.Prime 1344601 := by
  apply nodeValid_prime [2, 3, 5, 83] ⟨1344601, 17, [(2, 3), (3, 4), (5, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
  · decide +kernel

theorem prime_1630429 : Nat.Prime 1630429 := by
  apply nodeValid_prime [2, 3, 19, 7151] ⟨1630429, 2, [(2, 2), (3, 1), (19, 1), (7151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7151
  · decide +kernel

theorem prime_1794323 : Nat.Prime 1794323 := by
  apply nodeValid_prime [2, 19, 23, 2053] ⟨1794323, 2, [(2, 1), (19, 1), (23, 1), (2053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_2053
  · decide +kernel

theorem prime_1804871 : Nat.Prime 1804871 := by
  apply nodeValid_prime [2, 5, 101, 1787] ⟨1804871, 19, [(2, 1), (5, 1), (101, 1), (1787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_1787
  · decide +kernel

theorem prime_2253841 : Nat.Prime 2253841 := by
  apply nodeValid_prime [2, 3, 5, 9391] ⟨2253841, 13, [(2, 4), (3, 1), (5, 1), (9391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9391
  · decide +kernel

theorem prime_2352223 : Nat.Prime 2352223 := by
  apply nodeValid_prime [2, 3, 17, 7687] ⟨2352223, 3, [(2, 1), (3, 2), (17, 1), (7687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_7687
  · decide +kernel

theorem prime_2716061 : Nat.Prime 2716061 := by
  apply nodeValid_prime [2, 5, 139, 977] ⟨2716061, 2, [(2, 2), (5, 1), (139, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_977
  · decide +kernel

theorem prime_2725153 : Nat.Prime 2725153 := by
  apply nodeValid_prime [2, 3, 28387] ⟨2725153, 10, [(2, 5), (3, 1), (28387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28387
  · decide +kernel

theorem prime_3009931 : Nat.Prime 3009931 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 1303] ⟨3009931, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_1303
  · decide +kernel

theorem prime_3049181 : Nat.Prime 3049181 := by
  apply nodeValid_prime [2, 5, 152459] ⟨3049181, 3, [(2, 2), (5, 1), (152459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_152459
  · decide +kernel

theorem prime_3829219 : Nat.Prime 3829219 := by
  apply nodeValid_prime [2, 3, 29, 59, 373] ⟨3829219, 2, [(2, 1), (3, 1), (29, 1), (59, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_59
    · exact prime_373
  · decide +kernel

theorem prime_4486957 : Nat.Prime 4486957 := by
  apply nodeValid_prime [2, 3, 167, 2239] ⟨4486957, 2, [(2, 2), (3, 1), (167, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_2239
  · decide +kernel

theorem prime_4836977 : Nat.Prime 4836977 := by
  apply nodeValid_prime [2, 17, 17783] ⟨4836977, 3, [(2, 4), (17, 1), (17783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_17783
  · decide +kernel

theorem prime_5493049 : Nat.Prime 5493049 := by
  apply nodeValid_prime [2, 3, 11, 20807] ⟨5493049, 23, [(2, 3), (3, 1), (11, 1), (20807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_20807
  · decide +kernel

theorem prime_5643301 : Nat.Prime 5643301 := by
  apply nodeValid_prime [2, 3, 5, 13, 1447] ⟨5643301, 6, [(2, 2), (3, 1), (5, 2), (13, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1447
  · decide +kernel

theorem prime_6098363 : Nat.Prime 6098363 := by
  apply nodeValid_prime [2, 3049181] ⟨6098363, 2, [(2, 1), (3049181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3049181
  · decide +kernel

theorem prime_6762361 : Nat.Prime 6762361 := by
  apply nodeValid_prime [2, 3, 5, 11, 47, 109] ⟨6762361, 13, [(2, 3), (3, 1), (5, 1), (11, 1), (47, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_47
    · exact prime_109
  · decide +kernel

theorem prime_7207799 : Nat.Prime 7207799 := by
  apply nodeValid_prime [2, 13, 277223] ⟨7207799, 7, [(2, 1), (13, 1), (277223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_277223
  · decide +kernel

theorem prime_7738711 : Nat.Prime 7738711 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 857] ⟨7738711, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_857
  · decide +kernel

theorem prime_7864187 : Nat.Prime 7864187 := by
  apply nodeValid_prime [2, 11, 179, 1997] ⟨7864187, 5, [(2, 1), (11, 1), (179, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_179
    · exact prime_1997
  · decide +kernel

theorem prime_8497133 : Nat.Prime 8497133 := by
  apply nodeValid_prime [2, 7, 303469] ⟨8497133, 3, [(2, 2), (7, 1), (303469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_303469
  · decide +kernel

theorem prime_9090811 : Nat.Prime 9090811 := by
  apply nodeValid_prime [2, 3, 5, 101009] ⟨9090811, 2, [(2, 1), (3, 2), (5, 1), (101009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101009
  · decide +kernel

theorem prime_15462493 : Nat.Prime 15462493 := by
  apply nodeValid_prime [2, 3, 1288541] ⟨15462493, 2, [(2, 2), (3, 1), (1288541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1288541
  · decide +kernel

theorem prime_16994267 : Nat.Prime 16994267 := by
  apply nodeValid_prime [2, 8497133] ⟨16994267, 2, [(2, 1), (8497133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8497133
  · decide +kernel

theorem prime_17256461 : Nat.Prime 17256461 := by
  apply nodeValid_prime [2, 5, 13, 31, 2141] ⟨17256461, 3, [(2, 2), (5, 1), (13, 1), (31, 1), (2141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_31
    · exact prime_2141
  · decide +kernel

theorem prime_17488871 : Nat.Prime 17488871 := by
  apply nodeValid_prime [2, 5, 7, 433, 577] ⟨17488871, 7, [(2, 1), (5, 1), (7, 1), (433, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_433
    · exact prime_577
  · decide +kernel

theorem prime_19588631 : Nat.Prime 19588631 := by
  apply nodeValid_prime [2, 5, 29, 67547] ⟨19588631, 17, [(2, 1), (5, 1), (29, 1), (67547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_67547
  · decide +kernel

theorem prime_32050987 : Nat.Prime 32050987 := by
  apply nodeValid_prime [2, 3, 11, 19, 61, 419] ⟨32050987, 5, [(2, 1), (3, 1), (11, 1), (19, 1), (61, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_61
    · exact prime_419
  · decide +kernel

theorem prime_35786483 : Nat.Prime 35786483 := by
  apply nodeValid_prime [2, 23, 283, 2749] ⟨35786483, 2, [(2, 1), (23, 1), (283, 1), (2749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_283
    · exact prime_2749
  · decide +kernel

theorem prime_39130297 : Nat.Prime 39130297 := by
  apply nodeValid_prime [2, 3, 1630429] ⟨39130297, 5, [(2, 3), (3, 1), (1630429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1630429
  · decide +kernel

theorem prime_40338031 : Nat.Prime 40338031 := by
  apply nodeValid_prime [2, 3, 5, 1344601] ⟨40338031, 3, [(2, 1), (3, 1), (5, 1), (1344601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1344601
  · decide +kernel

theorem prime_41369767 : Nat.Prime 41369767 := by
  apply nodeValid_prime [2, 3, 229, 30109] ⟨41369767, 3, [(2, 1), (3, 1), (229, 1), (30109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_30109
  · decide +kernel

theorem prime_46368323 : Nat.Prime 46368323 := by
  apply nodeValid_prime [2, 7, 11, 13, 19, 23, 53] ⟨46368323, 2, [(2, 1), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_47185123 : Nat.Prime 47185123 := by
  apply nodeValid_prime [2, 3, 7864187] ⟨47185123, 3, [(2, 1), (3, 1), (7864187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7864187
  · decide +kernel

theorem prime_52305049 : Nat.Prime 52305049 := by
  apply nodeValid_prime [2, 3, 103, 2351] ⟨52305049, 7, [(2, 3), (3, 3), (103, 1), (2351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_2351
  · decide +kernel

theorem prime_103210319 : Nat.Prime 103210319 := by
  apply nodeValid_prime [2, 19, 2716061] ⟨103210319, 7, [(2, 1), (19, 1), (2716061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2716061
  · decide +kernel

theorem prime_185139947 : Nat.Prime 185139947 := by
  apply nodeValid_prime [2, 811, 114143] ⟨185139947, 2, [(2, 1), (811, 1), (114143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_811
    · exact prime_114143
  · decide +kernel

theorem prime_198136933 : Nat.Prime 198136933 := by
  apply nodeValid_prime [2, 3, 7, 29, 163, 499] ⟨198136933, 14, [(2, 2), (3, 1), (7, 1), (29, 1), (163, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_163
    · exact prime_499
  · decide +kernel

theorem prime_221738323 : Nat.Prime 221738323 := by
  apply nodeValid_prime [2, 3, 13, 19, 157, 953] ⟨221738323, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (157, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_157
    · exact prime_953
  · decide +kernel

theorem prime_261075379 : Nat.Prime 261075379 := by
  apply nodeValid_prime [2, 3, 71, 612853] ⟨261075379, 10, [(2, 1), (3, 1), (71, 1), (612853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_612853
  · decide +kernel

theorem prime_283110739 : Nat.Prime 283110739 := by
  apply nodeValid_prime [2, 3, 47185123] ⟨283110739, 7, [(2, 1), (3, 1), (47185123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47185123
  · decide +kernel

theorem prime_360085133 : Nat.Prime 360085133 := by
  apply nodeValid_prime [2, 11, 127, 64439] ⟨360085133, 2, [(2, 2), (11, 1), (127, 1), (64439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_127
    · exact prime_64439
  · decide +kernel

theorem prime_467047489 : Nat.Prime 467047489 := by
  apply nodeValid_prime [2, 3, 31, 131, 599] ⟨467047489, 7, [(2, 6), (3, 1), (31, 1), (131, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_131
    · exact prime_599
  · decide +kernel

theorem prime_514494109 : Nat.Prime 514494109 := by
  apply nodeValid_prime [2, 3, 53, 269651] ⟨514494109, 7, [(2, 2), (3, 2), (53, 1), (269651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_269651
  · decide +kernel

theorem prime_611793613 : Nat.Prime 611793613 := by
  apply nodeValid_prime [2, 3, 16994267] ⟨611793613, 2, [(2, 2), (3, 2), (16994267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16994267
  · decide +kernel

theorem prime_750636181 : Nat.Prime 750636181 := by
  apply nodeValid_prime [2, 3, 5, 7, 349, 569] ⟨750636181, 10, [(2, 2), (3, 3), (5, 1), (7, 1), (349, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_349
    · exact prime_569
  · decide +kernel

theorem prime_779646409 : Nat.Prime 779646409 := by
  apply nodeValid_prime [2, 3, 89, 365003] ⟨779646409, 19, [(2, 3), (3, 1), (89, 1), (365003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_365003
  · decide +kernel

theorem prime_821689087 : Nat.Prime 821689087 := by
  apply nodeValid_prime [2, 3, 19, 7207799] ⟨821689087, 3, [(2, 1), (3, 1), (19, 1), (7207799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7207799
  · decide +kernel

theorem prime_855852911 : Nat.Prime 855852911 := by
  apply nodeValid_prime [2, 5, 11, 19, 409499] ⟨855852911, 7, [(2, 1), (5, 1), (11, 1), (19, 1), (409499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_409499
  · decide +kernel

theorem prime_921873439 : Nat.Prime 921873439 := by
  apply nodeValid_prime [2, 3, 41, 1249151] ⟨921873439, 3, [(2, 1), (3, 2), (41, 1), (1249151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_1249151
  · decide +kernel

theorem prime_1475395447 : Nat.Prime 1475395447 := by
  apply nodeValid_prime [2, 3, 7, 43, 816941] ⟨1475395447, 7, [(2, 1), (3, 1), (7, 1), (43, 1), (816941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_816941
  · decide +kernel

theorem prime_1633252349 : Nat.Prime 1633252349 := by
  apply nodeValid_prime [2, 7, 13, 4486957] ⟨1633252349, 2, [(2, 2), (7, 1), (13, 1), (4486957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_4486957
  · decide +kernel

theorem prime_2116871741 : Nat.Prime 2116871741 := by
  apply nodeValid_prime [2, 5, 97, 643, 1697] ⟨2116871741, 2, [(2, 2), (5, 1), (97, 1), (643, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_643
    · exact prime_1697
  · decide +kernel

theorem prime_2938294651 : Nat.Prime 2938294651 := by
  apply nodeValid_prime [2, 3, 5, 19588631] ⟨2938294651, 19, [(2, 1), (3, 1), (5, 2), (19588631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19588631
  · decide +kernel

theorem prime_3687493757 : Nat.Prime 3687493757 := by
  apply nodeValid_prime [2, 921873439] ⟨3687493757, 2, [(2, 2), (921873439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_921873439
  · decide +kernel

theorem prime_3971497633 : Nat.Prime 3971497633 := by
  apply nodeValid_prime [2, 3, 41369767] ⟨3971497633, 7, [(2, 5), (3, 1), (41369767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41369767
  · decide +kernel

theorem prime_4152406561 : Nat.Prime 4152406561 := by
  apply nodeValid_prime [2, 3, 5, 131, 66037] ⟨4152406561, 11, [(2, 5), (3, 1), (5, 1), (131, 1), (66037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_66037
  · decide +kernel

theorem prime_8675509663 : Nat.Prime 8675509663 := by
  apply nodeValid_prime [2, 3, 79, 1367, 4463] ⟨8675509663, 3, [(2, 1), (3, 2), (79, 1), (1367, 1), (4463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_1367
    · exact prime_4463
  · decide +kernel

theorem prime_12007705397 : Nat.Prime 12007705397 := by
  apply nodeValid_prime [2, 271, 3083, 3593] ⟨12007705397, 2, [(2, 2), (271, 1), (3083, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_3083
    · exact prime_3593
  · decide +kernel

theorem prime_23828983603 : Nat.Prime 23828983603 := by
  apply nodeValid_prime [2, 3, 41, 59, 27827] ⟨23828983603, 2, [(2, 1), (3, 1), (41, 1), (59, 2), (27827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_59
    · exact prime_27827
  · decide +kernel

theorem prime_28987051231 : Nat.Prime 28987051231 := by
  apply nodeValid_prime [2, 3, 5, 35786483] ⟨28987051231, 3, [(2, 1), (3, 4), (5, 1), (35786483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_35786483
  · decide +kernel

theorem prime_72046232383 : Nat.Prime 72046232383 := by
  apply nodeValid_prime [2, 3, 12007705397] ⟨72046232383, 5, [(2, 1), (3, 1), (12007705397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12007705397
  · decide +kernel

theorem prime_144653952959 : Nat.Prime 144653952959 := by
  apply nodeValid_prime [2, 61, 21737, 54547] ⟨144653952959, 17, [(2, 1), (61, 1), (21737, 1), (54547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_21737
    · exact prime_54547
  · decide +kernel

theorem prime_149486622353 : Nat.Prime 149486622353 := by
  apply nodeValid_prime [2, 227, 1051, 39161] ⟨149486622353, 3, [(2, 4), (227, 1), (1051, 1), (39161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_1051
    · exact prime_39161
  · decide +kernel

theorem prime_285947802277 : Nat.Prime 285947802277 := by
  apply nodeValid_prime [2, 3, 29, 821689087] ⟨285947802277, 2, [(2, 2), (3, 1), (29, 1), (821689087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_821689087
  · decide +kernel

theorem prime_285947803237 : Nat.Prime 285947803237 := by
  apply nodeValid_prime [2, 3, 23828983603] ⟨285947803237, 5, [(2, 2), (3, 1), (23828983603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23828983603
  · decide +kernel

theorem prime_285947829577 : Nat.Prime 285947829577 := by
  apply nodeValid_prime [2, 3, 3971497633] ⟨285947829577, 5, [(2, 3), (3, 2), (3971497633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3971497633
  · decide +kernel

theorem prime_286505997341 : Nat.Prime 286505997341 := by
  apply nodeValid_prime [2, 5, 95917, 149351] ⟨286505997341, 2, [(2, 2), (5, 1), (95917, 1), (149351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_95917
    · exact prime_149351
  · decide +kernel

theorem prime_286505999477 : Nat.Prime 286505999477 := by
  apply nodeValid_prime [2, 7879, 9090811] ⟨286505999477, 2, [(2, 2), (7879, 1), (9090811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7879
    · exact prime_9090811
  · decide +kernel

theorem prime_286506005119 : Nat.Prime 286506005119 := by
  apply nodeValid_prime [2, 3, 241, 198136933] ⟨286506005119, 3, [(2, 1), (3, 1), (241, 1), (198136933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_198136933
  · decide +kernel

theorem prime_287064910997 : Nat.Prime 287064910997 := by
  apply nodeValid_prime [2, 37, 401, 4836977] ⟨287064910997, 2, [(2, 2), (37, 1), (401, 1), (4836977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_401
    · exact prime_4836977
  · decide +kernel

theorem prime_287064911179 : Nat.Prime 287064911179 := by
  apply nodeValid_prime [2, 3, 97, 1889, 87037] ⟨287064911179, 2, [(2, 1), (3, 2), (97, 1), (1889, 1), (87037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1889
    · exact prime_87037
  · decide +kernel

theorem prime_287064912829 : Nat.Prime 287064912829 := by
  apply nodeValid_prime [2, 3, 69911, 342179] ⟨287064912829, 2, [(2, 2), (3, 1), (69911, 1), (342179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_69911
    · exact prime_342179
  · decide +kernel

theorem prime_287624513047 : Nat.Prime 287624513047 := by
  apply nodeValid_prime [2, 3, 13, 3687493757] ⟨287624513047, 5, [(2, 1), (3, 1), (13, 1), (3687493757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3687493757
  · decide +kernel

theorem prime_287624513773 : Nat.Prime 287624513773 := by
  apply nodeValid_prime [2, 3, 38053, 209959] ⟨287624513773, 14, [(2, 2), (3, 2), (38053, 1), (209959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_38053
    · exact prime_209959
  · decide +kernel

theorem prime_287624553371 : Nat.Prime 287624553371 := by
  apply nodeValid_prime [2, 5, 7, 11, 59, 149, 42491] ⟨287624553371, 2, [(2, 1), (5, 1), (7, 1), (11, 1), (59, 1), (149, 1), (42491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_59
    · exact prime_149
    · exact prime_42491
  · decide +kernel

theorem prime_288184929533 : Nat.Prime 288184929533 := by
  apply nodeValid_prime [2, 72046232383] ⟨288184929533, 2, [(2, 2), (72046232383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_72046232383
  · decide +kernel

theorem prime_288184929751 : Nat.Prime 288184929751 := by
  apply nodeValid_prime [2, 3, 5, 47, 2725153] ⟨288184929751, 3, [(2, 1), (3, 2), (5, 3), (47, 1), (2725153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_2725153
  · decide +kernel

theorem prime_288184931123 : Nat.Prime 288184931123 := by
  apply nodeValid_prime [2, 11, 23, 29, 59, 127, 2621] ⟨288184931123, 2, [(2, 1), (11, 1), (23, 1), (29, 1), (59, 1), (127, 1), (2621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_29
    · exact prime_59
    · exact prime_127
    · exact prime_2621
  · decide +kernel

theorem prime_288746029217 : Nat.Prime 288746029217 := by
  apply nodeValid_prime [2, 163, 173, 433, 739] ⟨288746029217, 3, [(2, 5), (163, 1), (173, 1), (433, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_173
    · exact prime_433
    · exact prime_739
  · decide +kernel

theorem prime_288746030423 : Nat.Prime 288746030423 := by
  apply nodeValid_prime [2, 1213, 8951, 13297] ⟨288746030423, 5, [(2, 1), (1213, 1), (8951, 1), (13297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1213
    · exact prime_8951
    · exact prime_13297
  · decide +kernel

theorem prime_288746045807 : Nat.Prime 288746045807 := by
  apply nodeValid_prime [2, 17, 4733, 1794323] ⟨288746045807, 5, [(2, 1), (17, 1), (4733, 1), (1794323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4733
    · exact prime_1794323
  · decide +kernel

theorem prime_289307900503 : Nat.Prime 289307900503 := by
  apply nodeValid_prime [2, 3, 37, 71, 367, 5557] ⟨289307900503, 3, [(2, 1), (3, 3), (37, 1), (71, 1), (367, 1), (5557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_71
    · exact prime_367
    · exact prime_5557
  · decide +kernel

theorem prime_289307904733 : Nat.Prime 289307904733 := by
  apply nodeValid_prime [2, 3, 7, 11, 19, 5493049] ⟨289307904733, 5, [(2, 2), (3, 2), (7, 1), (11, 1), (19, 1), (5493049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_5493049
  · decide +kernel

theorem prime_289307905919 : Nat.Prime 289307905919 := by
  apply nodeValid_prime [2, 144653952959] ⟨289307905919, 7, [(2, 1), (144653952959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_144653952959
  · decide +kernel

theorem prime_289870498597 : Nat.Prime 289870498597 := by
  apply nodeValid_prime [2, 3, 7, 22153, 155773] ⟨289870498597, 2, [(2, 2), (3, 1), (7, 1), (22153, 1), (155773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_22153
    · exact prime_155773
  · decide +kernel

theorem prime_289870512311 : Nat.Prime 289870512311 := by
  apply nodeValid_prime [2, 5, 28987051231] ⟨289870512311, 7, [(2, 1), (5, 1), (28987051231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_28987051231
  · decide +kernel

theorem prime_289870512629 : Nat.Prime 289870512629 := by
  apply nodeValid_prime [2, 89, 1523, 534631] ⟨289870512629, 2, [(2, 2), (89, 1), (1523, 1), (534631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_1523
    · exact prime_534631
  · decide +kernel

theorem prime_290433823201 : Nat.Prime 290433823201 := by
  apply nodeValid_prime [2, 3, 5, 40338031] ⟨290433823201, 29, [(2, 5), (3, 2), (5, 2), (40338031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_40338031
  · decide +kernel

theorem prime_290433823831 : Nat.Prime 290433823831 := by
  apply nodeValid_prime [2, 3, 5, 139, 7738711] ⟨290433823831, 3, [(2, 1), (3, 3), (5, 1), (139, 1), (7738711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_7738711
  · decide +kernel

theorem prime_290433837667 : Nat.Prime 290433837667 := by
  apply nodeValid_prime [2, 3, 7, 67, 103210319] ⟨290433837667, 3, [(2, 1), (3, 1), (7, 1), (67, 1), (103210319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
    · exact prime_103210319
  · decide +kernel

theorem prime_290997918553 : Nat.Prime 290997918553 := by
  apply nodeValid_prime [2, 3, 11, 163, 6762361] ⟨290997918553, 5, [(2, 3), (3, 1), (11, 1), (163, 1), (6762361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_163
    · exact prime_6762361
  · decide +kernel

theorem prime_290997919193 : Nat.Prime 290997919193 := by
  apply nodeValid_prime [2, 16139, 2253841] ⟨290997919193, 3, [(2, 3), (16139, 1), (2253841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16139
    · exact prime_2253841
  · decide +kernel

theorem prime_291562735031 : Nat.Prime 291562735031 := by
  apply nodeValid_prime [2, 5, 7, 683, 6098363] ⟨291562735031, 7, [(2, 1), (5, 1), (7, 1), (683, 1), (6098363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_683
    · exact prime_6098363
  · decide +kernel

theorem prime_291562738463 : Nat.Prime 291562738463 := by
  apply nodeValid_prime [2, 139, 1061, 988489] ⟨291562738463, 5, [(2, 1), (139, 1), (1061, 1), (988489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_1061
    · exact prime_988489
  · decide +kernel

theorem prime_291562745297 : Nat.Prime 291562745297 := by
  apply nodeValid_prime [2, 61, 127, 2352223] ⟨291562745297, 3, [(2, 4), (61, 1), (127, 1), (2352223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_127
    · exact prime_2352223
  · decide +kernel

theorem prime_292128298507 : Nat.Prime 292128298507 := by
  apply nodeValid_prime [2, 3, 11, 1475395447] ⟨292128298507, 2, [(2, 1), (3, 2), (11, 1), (1475395447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1475395447
  · decide +kernel

theorem prime_292128300259 : Nat.Prime 292128300259 := by
  apply nodeValid_prime [2, 3, 23, 2116871741] ⟨292128300259, 2, [(2, 1), (3, 1), (23, 1), (2116871741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2116871741
  · decide +kernel

theorem prime_292128311753 : Nat.Prime 292128311753 := by
  apply nodeValid_prime [2, 67, 419, 449, 2897] ⟨292128311753, 3, [(2, 3), (67, 1), (419, 1), (449, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_419
    · exact prime_449
    · exact prime_2897
  · decide +kernel

theorem prime_292694586361 : Nat.Prime 292694586361 := by
  apply nodeValid_prime [2, 3, 5, 11, 221738323] ⟨292694586361, 29, [(2, 3), (3, 1), (5, 1), (11, 1), (221738323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_221738323
  · decide +kernel

theorem prime_292694587093 : Nat.Prime 292694587093 := by
  apply nodeValid_prime [2, 3, 19, 37, 457, 25307] ⟨292694587093, 6, [(2, 2), (3, 2), (19, 1), (37, 1), (457, 1), (25307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
    · exact prime_457
    · exact prime_25307
  · decide +kernel

theorem prime_292694621561 : Nat.Prime 292694621561 := by
  apply nodeValid_prime [2, 5, 11, 17, 39130297] ⟨292694621561, 3, [(2, 3), (5, 1), (11, 1), (17, 1), (39130297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_39130297
  · decide +kernel

theorem prime_293261642131 : Nat.Prime 293261642131 := by
  apply nodeValid_prime [2, 3, 5, 19, 514494109] ⟨293261642131, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (514494109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_514494109
  · decide +kernel

theorem prime_293261642239 : Nat.Prime 293261642239 := by
  apply nodeValid_prime [2, 3, 29, 109, 15462493] ⟨293261642239, 6, [(2, 1), (3, 1), (29, 1), (109, 1), (15462493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_109
    · exact prime_15462493
  · decide +kernel

theorem prime_293261676049 : Nat.Prime 293261676049 := by
  apply nodeValid_prime [2, 3, 11, 185139947] ⟨293261676049, 14, [(2, 4), (3, 2), (11, 1), (185139947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_185139947
  · decide +kernel

theorem prime_293829464221 : Nat.Prime 293829464221 := by
  apply nodeValid_prime [2, 3, 5, 1627, 3009931] ⟨293829464221, 6, [(2, 2), (3, 1), (5, 1), (1627, 1), (3009931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1627
    · exact prime_3009931
  · decide +kernel

theorem prime_293829465101 : Nat.Prime 293829465101 := by
  apply nodeValid_prime [2, 5, 2938294651] ⟨293829465101, 2, [(2, 2), (5, 2), (2938294651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2938294651
  · decide +kernel

theorem prime_293829468529 : Nat.Prime 293829468529 := by
  apply nodeValid_prime [2, 3, 17, 360085133] ⟨293829468529, 19, [(2, 4), (3, 1), (17, 1), (360085133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_360085133
  · decide +kernel

theorem prime_294398010941 : Nat.Prime 294398010941 := by
  apply nodeValid_prime [2, 5, 11, 601, 1039, 2143] ⟨294398010941, 3, [(2, 2), (5, 1), (11, 1), (601, 1), (1039, 1), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_601
    · exact prime_1039
    · exact prime_2143
  · decide +kernel

theorem prime_294398015111 : Nat.Prime 294398015111 := by
  apply nodeValid_prime [2, 5, 31271, 941441] ⟨294398015111, 7, [(2, 1), (5, 1), (31271, 1), (941441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31271
    · exact prime_941441
  · decide +kernel

theorem prime_294398015159 : Nat.Prime 294398015159 := by
  apply nodeValid_prime [2, 13, 2957, 3829219] ⟨294398015159, 23, [(2, 1), (13, 1), (2957, 1), (3829219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2957
    · exact prime_3829219
  · decide +kernel

theorem prime_294967298287 : Nat.Prime 294967298287 := by
  apply nodeValid_prime [2, 3, 937, 17488871] ⟨294967298287, 3, [(2, 1), (3, 2), (937, 1), (17488871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_937
    · exact prime_17488871
  · decide +kernel

theorem prime_294967328543 : Nat.Prime 294967328543 := by
  apply nodeValid_prime [2, 17, 8675509663] ⟨294967328543, 5, [(2, 1), (17, 1), (8675509663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_8675509663
  · decide +kernel

theorem prime_294967328969 : Nat.Prime 294967328969 := by
  apply nodeValid_prime [2, 13, 31, 8273, 11059] ⟨294967328969, 3, [(2, 3), (13, 1), (31, 1), (8273, 1), (11059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_8273
    · exact prime_11059
  · decide +kernel

theorem prime_295537329029 : Nat.Prime 295537329029 := by
  apply nodeValid_prime [2, 283, 261075379] ⟨295537329029, 2, [(2, 2), (283, 1), (261075379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_261075379
  · decide +kernel

theorem prime_295537337591 : Nat.Prime 295537337591 := by
  apply nodeValid_prime [2, 5, 11, 17, 1453, 108769] ⟨295537337591, 13, [(2, 1), (5, 1), (11, 1), (17, 1), (1453, 1), (108769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_1453
    · exact prime_108769
  · decide +kernel

theorem prime_295537337857 : Nat.Prime 295537337857 := by
  apply nodeValid_prime [2, 3, 23, 101, 9203] ⟨295537337857, 15, [(2, 9), (3, 3), (23, 1), (101, 1), (9203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_101
    · exact prime_9203
  · decide +kernel

theorem prime_296108108027 : Nat.Prime 296108108027 := by
  apply nodeValid_prime [2, 317, 467047489] ⟨296108108027, 2, [(2, 1), (317, 1), (467047489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_467047489
  · decide +kernel

theorem prime_296108108693 : Nat.Prime 296108108693 := by
  apply nodeValid_prime [2, 11, 611793613] ⟨296108108693, 2, [(2, 2), (11, 2), (611793613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_611793613
  · decide +kernel

theorem prime_296108110679 : Nat.Prime 296108110679 := by
  apply nodeValid_prime [2, 31, 103, 46368323] ⟨296108110679, 17, [(2, 1), (31, 1), (103, 1), (46368323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_103
    · exact prime_46368323
  · decide +kernel

theorem prime_296679620173 : Nat.Prime 296679620173 := by
  apply nodeValid_prime [2, 3, 13, 337, 5643301] ⟨296679620173, 2, [(2, 2), (3, 1), (13, 1), (337, 1), (5643301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_337
    · exact prime_5643301
  · decide +kernel

theorem prime_296679620767 : Nat.Prime 296679620767 := by
  apply nodeValid_prime [2, 3, 17, 16691, 174263] ⟨296679620767, 3, [(2, 1), (3, 1), (17, 1), (16691, 1), (174263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_16691
    · exact prime_174263
  · decide +kernel

theorem prime_296679643961 : Nat.Prime 296679643961 := by
  apply nodeValid_prime [2, 5, 7, 853, 1242169] ⟨296679643961, 3, [(2, 3), (5, 1), (7, 1), (853, 1), (1242169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_853
    · exact prime_1242169
  · decide +kernel

theorem prime_297251925031 : Nat.Prime 297251925031 := by
  apply nodeValid_prime [2, 3, 5, 89, 337, 110119] ⟨297251925031, 6, [(2, 1), (3, 2), (5, 1), (89, 1), (337, 1), (110119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_337
    · exact prime_110119
  · decide +kernel

theorem prime_297251927519 : Nat.Prime 297251927519 := by
  apply nodeValid_prime [2, 7, 13, 1633252349] ⟨297251927519, 14, [(2, 1), (7, 1), (13, 1), (1633252349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1633252349
  · decide +kernel

theorem prime_297251927677 : Nat.Prime 297251927677 := by
  apply nodeValid_prime [2, 3, 11, 750636181] ⟨297251927677, 2, [(2, 2), (3, 2), (11, 1), (750636181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_750636181
  · decide +kernel

theorem prime_297824928239 : Nat.Prime 297824928239 := by
  apply nodeValid_prime [2, 191, 779646409] ⟨297824928239, 11, [(2, 1), (191, 1), (779646409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_779646409
  · decide +kernel

theorem prime_297824929189 : Nat.Prime 297824929189 := by
  apply nodeValid_prime [2, 3, 34651, 716249] ⟨297824929189, 2, [(2, 2), (3, 1), (34651, 1), (716249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34651
    · exact prime_716249
  · decide +kernel

theorem prime_297824949007 : Nat.Prime 297824949007 := by
  apply nodeValid_prime [2, 3, 13, 73, 52305049] ⟨297824949007, 3, [(2, 1), (3, 1), (13, 1), (73, 1), (52305049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
    · exact prime_52305049
  · decide +kernel

theorem prime_298398718907 : Nat.Prime 298398718907 := by
  apply nodeValid_prime [2, 17, 31, 283110739] ⟨298398718907, 5, [(2, 1), (17, 1), (31, 1), (283110739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_283110739
  · decide +kernel

theorem prime_298398723613 : Nat.Prime 298398723613 := by
  apply nodeValid_prime [2, 3, 11, 131, 17256461] ⟨298398723613, 2, [(2, 2), (3, 1), (11, 1), (131, 1), (17256461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
    · exact prime_17256461
  · decide +kernel

theorem prime_298398723757 : Nat.Prime 298398723757 := by
  apply nodeValid_prime [2, 3, 7, 29, 1129, 108499] ⟨298398723757, 5, [(2, 2), (3, 1), (7, 1), (29, 1), (1129, 1), (108499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_1129
    · exact prime_108499
  · decide +kernel

theorem prime_298973244707 : Nat.Prime 298973244707 := by
  apply nodeValid_prime [2, 149486622353] ⟨298973244707, 2, [(2, 1), (149486622353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_149486622353
  · decide +kernel

theorem prime_298973271409 : Nat.Prime 298973271409 := by
  apply nodeValid_prime [2, 3, 7, 17, 29, 1804871] ⟨298973271409, 11, [(2, 4), (3, 1), (7, 1), (17, 1), (29, 1), (1804871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_29
    · exact prime_1804871
  · decide +kernel

theorem prime_298973272393 : Nat.Prime 298973272393 := by
  apply nodeValid_prime [2, 3, 4152406561] ⟨298973272393, 5, [(2, 3), (3, 2), (4152406561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4152406561
  · decide +kernel

theorem prime_299548518851 : Nat.Prime 299548518851 := by
  apply nodeValid_prime [2, 5, 7, 855852911] ⟨299548518851, 2, [(2, 1), (5, 2), (7, 1), (855852911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_855852911
  · decide +kernel

theorem prime_299548524439 : Nat.Prime 299548524439 := by
  apply nodeValid_prime [2, 3, 55213, 100469] ⟨299548524439, 3, [(2, 1), (3, 3), (55213, 1), (100469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55213
    · exact prime_100469
  · decide +kernel

theorem prime_299548524503 : Nat.Prime 299548524503 := by
  apply nodeValid_prime [2, 4673, 32050987] ⟨299548524503, 5, [(2, 1), (4673, 1), (32050987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4673
    · exact prime_32050987
  · decide +kernel

end Sude.Lucas.Generated
