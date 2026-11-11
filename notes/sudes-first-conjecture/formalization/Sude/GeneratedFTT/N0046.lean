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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3767 : Nat.Prime 3767 := by
  apply nodeValid_prime [2, 7, 269] ⟨3767, 5, [(2, 1), (7, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_269
  · decide +kernel

theorem prime_5939 : Nat.Prime 5939 := by
  apply nodeValid_prime [2, 2969] ⟨5939, 2, [(2, 1), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2969
  · decide +kernel

theorem prime_6997 : Nat.Prime 6997 := by
  apply nodeValid_prime [2, 3, 11, 53] ⟨6997, 5, [(2, 2), (3, 1), (11, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
  · decide +kernel

theorem prime_8269 : Nat.Prime 8269 := by
  apply nodeValid_prime [2, 3, 13, 53] ⟨8269, 2, [(2, 2), (3, 1), (13, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_10477 : Nat.Prime 10477 := by
  apply nodeValid_prime [2, 3, 97] ⟨10477, 2, [(2, 2), (3, 3), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
  · decide +kernel

theorem prime_10753 : Nat.Prime 10753 := by
  apply nodeValid_prime [2, 3, 7] ⟨10753, 11, [(2, 9), (3, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_11827 : Nat.Prime 11827 := by
  apply nodeValid_prime [2, 3, 73] ⟨11827, 2, [(2, 1), (3, 4), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
  · decide +kernel

theorem prime_12101 : Nat.Prime 12101 := by
  apply nodeValid_prime [2, 5, 11] ⟨12101, 3, [(2, 2), (5, 2), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_12491 : Nat.Prime 12491 := by
  apply nodeValid_prime [2, 5, 1249] ⟨12491, 2, [(2, 1), (5, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1249
  · decide +kernel

theorem prime_13451 : Nat.Prime 13451 := by
  apply nodeValid_prime [2, 5, 269] ⟨13451, 2, [(2, 1), (5, 2), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
  · decide +kernel

theorem prime_16561 : Nat.Prime 16561 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨16561, 7, [(2, 4), (3, 2), (5, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_18587 : Nat.Prime 18587 := by
  apply nodeValid_prime [2, 9293] ⟨18587, 2, [(2, 1), (9293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9293
  · decide +kernel

theorem prime_20047 : Nat.Prime 20047 := by
  apply nodeValid_prime [2, 3, 13, 257] ⟨20047, 3, [(2, 1), (3, 1), (13, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_257
  · decide +kernel

theorem prime_20219 : Nat.Prime 20219 := by
  apply nodeValid_prime [2, 11, 919] ⟨20219, 2, [(2, 1), (11, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_919
  · decide +kernel

theorem prime_22171 : Nat.Prime 22171 := by
  apply nodeValid_prime [2, 3, 5, 739] ⟨22171, 2, [(2, 1), (3, 1), (5, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_739
  · decide +kernel

theorem prime_23623 : Nat.Prime 23623 := by
  apply nodeValid_prime [2, 3, 31, 127] ⟨23623, 6, [(2, 1), (3, 1), (31, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_127
  · decide +kernel

theorem prime_24203 : Nat.Prime 24203 := by
  apply nodeValid_prime [2, 12101] ⟨24203, 2, [(2, 1), (12101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12101
  · decide +kernel

theorem prime_25423 : Nat.Prime 25423 := by
  apply nodeValid_prime [2, 3, 19, 223] ⟨25423, 3, [(2, 1), (3, 1), (19, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_223
  · decide +kernel

theorem prime_29021 : Nat.Prime 29021 := by
  apply nodeValid_prime [2, 5, 1451] ⟨29021, 2, [(2, 2), (5, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1451
  · decide +kernel

theorem prime_32719 : Nat.Prime 32719 := by
  apply nodeValid_prime [2, 3, 7, 19, 41] ⟨32719, 3, [(2, 1), (3, 1), (7, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_37967 : Nat.Prime 37967 := by
  apply nodeValid_prime [2, 41, 463] ⟨37967, 5, [(2, 1), (41, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_463
  · decide +kernel

theorem prime_41039 : Nat.Prime 41039 := by
  apply nodeValid_prime [2, 17, 71] ⟨41039, 11, [(2, 1), (17, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_41149 : Nat.Prime 41149 := by
  apply nodeValid_prime [2, 3, 127] ⟨41149, 2, [(2, 2), (3, 4), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
  · decide +kernel

theorem prime_42061 : Nat.Prime 42061 := by
  apply nodeValid_prime [2, 3, 5, 701] ⟨42061, 6, [(2, 2), (3, 1), (5, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_701
  · decide +kernel

theorem prime_44917 : Nat.Prime 44917 := by
  apply nodeValid_prime [2, 3, 19, 197] ⟨44917, 5, [(2, 2), (3, 1), (19, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_197
  · decide +kernel

theorem prime_70181 : Nat.Prime 70181 := by
  apply nodeValid_prime [2, 5, 11, 29] ⟨70181, 7, [(2, 2), (5, 1), (11, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_71327 : Nat.Prime 71327 := by
  apply nodeValid_prime [2, 19, 1877] ⟨71327, 5, [(2, 1), (19, 1), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1877
  · decide +kernel

theorem prime_74381 : Nat.Prime 74381 := by
  apply nodeValid_prime [2, 5, 3719] ⟨74381, 2, [(2, 2), (5, 1), (3719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3719
  · decide +kernel

theorem prime_74449 : Nat.Prime 74449 := by
  apply nodeValid_prime [2, 3, 11, 47] ⟨74449, 13, [(2, 4), (3, 2), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_85009 : Nat.Prime 85009 := by
  apply nodeValid_prime [2, 3, 7, 11, 23] ⟨85009, 13, [(2, 4), (3, 1), (7, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_87293 : Nat.Prime 87293 := by
  apply nodeValid_prime [2, 139, 157] ⟨87293, 2, [(2, 2), (139, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_157
  · decide +kernel

theorem prime_87589 : Nat.Prime 87589 := by
  apply nodeValid_prime [2, 3, 811] ⟨87589, 2, [(2, 2), (3, 3), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
  · decide +kernel

theorem prime_92051 : Nat.Prime 92051 := by
  apply nodeValid_prime [2, 5, 7, 263] ⟨92051, 6, [(2, 1), (5, 2), (7, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_263
  · decide +kernel

theorem prime_96703 : Nat.Prime 96703 := by
  apply nodeValid_prime [2, 3, 71, 227] ⟨96703, 3, [(2, 1), (3, 1), (71, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_227
  · decide +kernel

theorem prime_100493 : Nat.Prime 100493 := by
  apply nodeValid_prime [2, 7, 37, 97] ⟨100493, 2, [(2, 2), (7, 1), (37, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_97
  · decide +kernel

theorem prime_104473 : Nat.Prime 104473 := by
  apply nodeValid_prime [2, 3, 1451] ⟨104473, 5, [(2, 3), (3, 2), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
  · decide +kernel

theorem prime_111833 : Nat.Prime 111833 := by
  apply nodeValid_prime [2, 7, 1997] ⟨111833, 3, [(2, 3), (7, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1997
  · decide +kernel

theorem prime_113117 : Nat.Prime 113117 := by
  apply nodeValid_prime [2, 28279] ⟨113117, 2, [(2, 2), (28279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28279
  · decide +kernel

theorem prime_115363 : Nat.Prime 115363 := by
  apply nodeValid_prime [2, 3, 13, 17, 29] ⟨115363, 3, [(2, 1), (3, 2), (13, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_121501 : Nat.Prime 121501 := by
  apply nodeValid_prime [2, 3, 5] ⟨121501, 2, [(2, 2), (3, 5), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_140363 : Nat.Prime 140363 := by
  apply nodeValid_prime [2, 70181] ⟨140363, 2, [(2, 1), (70181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_70181
  · decide +kernel

theorem prime_148711 : Nat.Prime 148711 := by
  apply nodeValid_prime [2, 3, 5, 4957] ⟨148711, 15, [(2, 1), (3, 1), (5, 1), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4957
  · decide +kernel

theorem prime_161507 : Nat.Prime 161507 := by
  apply nodeValid_prime [2, 23, 3511] ⟨161507, 2, [(2, 1), (23, 1), (3511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_3511
  · decide +kernel

theorem prime_161753 : Nat.Prime 161753 := by
  apply nodeValid_prime [2, 20219] ⟨161753, 3, [(2, 3), (20219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20219
  · decide +kernel

theorem prime_167633 : Nat.Prime 167633 := by
  apply nodeValid_prime [2, 10477] ⟨167633, 3, [(2, 4), (10477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10477
  · decide +kernel

theorem prime_180511 : Nat.Prime 180511 := by
  apply nodeValid_prime [2, 3, 5, 11, 547] ⟨180511, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_547
  · decide +kernel

theorem prime_203419 : Nat.Prime 203419 := by
  apply nodeValid_prime [2, 3, 3767] ⟨203419, 3, [(2, 1), (3, 3), (3767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3767
  · decide +kernel

theorem prime_215389 : Nat.Prime 215389 := by
  apply nodeValid_prime [2, 3, 31, 193] ⟨215389, 2, [(2, 2), (3, 2), (31, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_193
  · decide +kernel

theorem prime_216569 : Nat.Prime 216569 := by
  apply nodeValid_prime [2, 11, 23, 107] ⟨216569, 3, [(2, 3), (11, 1), (23, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_107
  · decide +kernel

theorem prime_266053 : Nat.Prime 266053 := by
  apply nodeValid_prime [2, 3, 22171] ⟨266053, 2, [(2, 2), (3, 1), (22171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22171
  · decide +kernel

theorem prime_270527 : Nat.Prime 270527 := by
  apply nodeValid_prime [2, 23, 5881] ⟨270527, 5, [(2, 1), (23, 1), (5881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_5881
  · decide +kernel

theorem prime_290761 : Nat.Prime 290761 := by
  apply nodeValid_prime [2, 3, 5, 2423] ⟨290761, 31, [(2, 3), (3, 1), (5, 1), (2423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2423
  · decide +kernel

theorem prime_388691 : Nat.Prime 388691 := by
  apply nodeValid_prime [2, 5, 47, 827] ⟨388691, 2, [(2, 1), (5, 1), (47, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_827
  · decide +kernel

theorem prime_394819 : Nat.Prime 394819 := by
  apply nodeValid_prime [2, 3, 23, 2861] ⟨394819, 2, [(2, 1), (3, 1), (23, 1), (2861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_2861
  · decide +kernel

theorem prime_411491 : Nat.Prime 411491 := by
  apply nodeValid_prime [2, 5, 41149] ⟨411491, 2, [(2, 1), (5, 1), (41149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41149
  · decide +kernel

theorem prime_465841 : Nat.Prime 465841 := by
  apply nodeValid_prime [2, 3, 5, 647] ⟨465841, 7, [(2, 4), (3, 2), (5, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_647
  · decide +kernel

theorem prime_494129 : Nat.Prime 494129 := by
  apply nodeValid_prime [2, 89, 347] ⟨494129, 3, [(2, 4), (89, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_347
  · decide +kernel

theorem prime_598229 : Nat.Prime 598229 := by
  apply nodeValid_prime [2, 347, 431] ⟨598229, 2, [(2, 2), (347, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_431
  · decide +kernel

theorem prime_628591 : Nat.Prime 628591 := by
  apply nodeValid_prime [2, 3, 5, 23, 911] ⟨628591, 6, [(2, 1), (3, 1), (5, 1), (23, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_911
  · decide +kernel

theorem prime_660073 : Nat.Prime 660073 := by
  apply nodeValid_prime [2, 3, 7, 3929] ⟨660073, 10, [(2, 3), (3, 1), (7, 1), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3929
  · decide +kernel

theorem prime_717751 : Nat.Prime 717751 := by
  apply nodeValid_prime [2, 3, 5, 11, 29] ⟨717751, 3, [(2, 1), (3, 2), (5, 3), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_723479 : Nat.Prime 723479 := by
  apply nodeValid_prime [2, 7, 31, 1667] ⟨723479, 11, [(2, 1), (7, 1), (31, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_1667
  · decide +kernel

theorem prime_736409 : Nat.Prime 736409 := by
  apply nodeValid_prime [2, 92051] ⟨736409, 3, [(2, 3), (92051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92051
  · decide +kernel

theorem prime_828811 : Nat.Prime 828811 := by
  apply nodeValid_prime [2, 3, 5, 9209] ⟨828811, 3, [(2, 1), (3, 2), (5, 1), (9209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9209
  · decide +kernel

theorem prime_1020109 : Nat.Prime 1020109 := by
  apply nodeValid_prime [2, 3, 85009] ⟨1020109, 2, [(2, 2), (3, 1), (85009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_85009
  · decide +kernel

theorem prime_1103561 : Nat.Prime 1103561 := by
  apply nodeValid_prime [2, 5, 47, 587] ⟨1103561, 3, [(2, 3), (5, 1), (47, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_587
  · decide +kernel

theorem prime_1188037 : Nat.Prime 1188037 := by
  apply nodeValid_prime [2, 3, 61, 541] ⟨1188037, 2, [(2, 2), (3, 2), (61, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_541
  · decide +kernel

theorem prime_1514197 : Nat.Prime 1514197 := by
  apply nodeValid_prime [2, 3, 42061] ⟨1514197, 2, [(2, 2), (3, 2), (42061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42061
  · decide +kernel

theorem prime_1623163 : Nat.Prime 1623163 := by
  apply nodeValid_prime [2, 3, 270527] ⟨1623163, 5, [(2, 1), (3, 1), (270527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_270527
  · decide +kernel

theorem prime_2264543 : Nat.Prime 2264543 := by
  apply nodeValid_prime [2, 7, 161753] ⟨2264543, 5, [(2, 1), (7, 1), (161753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_161753
  · decide +kernel

theorem prime_2283551 : Nat.Prime 2283551 := by
  apply nodeValid_prime [2, 5, 109, 419] ⟨2283551, 7, [(2, 1), (5, 2), (109, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_419
  · decide +kernel

theorem prime_2460797 : Nat.Prime 2460797 := by
  apply nodeValid_prime [2, 13, 37, 1279] ⟨2460797, 2, [(2, 2), (13, 1), (37, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_1279
  · decide +kernel

theorem prime_2736511 : Nat.Prime 2736511 := by
  apply nodeValid_prime [2, 3, 5, 7, 83, 157] ⟨2736511, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (83, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_83
    · exact prime_157
  · decide +kernel

theorem prime_4466941 : Nat.Prime 4466941 := by
  apply nodeValid_prime [2, 3, 5, 74449] ⟨4466941, 7, [(2, 2), (3, 1), (5, 1), (74449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_74449
  · decide +kernel

theorem prime_6600731 : Nat.Prime 6600731 := by
  apply nodeValid_prime [2, 5, 660073] ⟨6600731, 2, [(2, 1), (5, 1), (660073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_660073
  · decide +kernel

theorem prime_7220441 : Nat.Prime 7220441 := by
  apply nodeValid_prime [2, 5, 180511] ⟨7220441, 3, [(2, 3), (5, 1), (180511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_180511
  · decide +kernel

theorem prime_12891971 : Nat.Prime 12891971 := by
  apply nodeValid_prime [2, 5, 7, 13, 31, 457] ⟨12891971, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (31, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_457
  · decide +kernel

theorem prime_13121573 : Nat.Prime 13121573 := by
  apply nodeValid_prime [2, 29, 113117] ⟨13121573, 3, [(2, 2), (29, 1), (113117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_113117
  · decide +kernel

theorem prime_19831237 : Nat.Prime 19831237 := by
  apply nodeValid_prime [2, 3, 967, 1709] ⟨19831237, 2, [(2, 2), (3, 1), (967, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
    · exact prime_1709
  · decide +kernel

theorem prime_19864099 : Nat.Prime 19864099 := by
  apply nodeValid_prime [2, 3, 1103561] ⟨19864099, 3, [(2, 1), (3, 2), (1103561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1103561
  · decide +kernel

theorem prime_21575201 : Nat.Prime 21575201 := by
  apply nodeValid_prime [2, 5, 149, 181] ⟨21575201, 3, [(2, 5), (5, 2), (149, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_181
  · decide +kernel

theorem prime_22455101 : Nat.Prime 22455101 := by
  apply nodeValid_prime [2, 5, 431, 521] ⟨22455101, 3, [(2, 2), (5, 2), (431, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_431
    · exact prime_521
  · decide +kernel

theorem prime_22912009 : Nat.Prime 22912009 := by
  apply nodeValid_prime [2, 3, 7, 19483] ⟨22912009, 11, [(2, 3), (3, 1), (7, 2), (19483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19483
  · decide +kernel

theorem prime_32801231 : Nat.Prime 32801231 := by
  apply nodeValid_prime [2, 5, 7, 11, 41, 1039] ⟨32801231, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (41, 1), (1039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_41
    · exact prime_1039
  · decide +kernel

theorem prime_42499843 : Nat.Prime 42499843 := by
  apply nodeValid_prime [2, 3, 7, 11, 67, 1373] ⟨42499843, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (67, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_67
    · exact prime_1373
  · decide +kernel

theorem prime_43098173 : Nat.Prime 43098173 := by
  apply nodeValid_prime [2, 13, 828811] ⟨43098173, 2, [(2, 2), (13, 1), (828811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_828811
  · decide +kernel

theorem prime_44037683 : Nat.Prime 44037683 := by
  apply nodeValid_prime [2, 13, 113, 1153] ⟨44037683, 2, [(2, 1), (13, 2), (113, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
    · exact prime_1153
  · decide +kernel

theorem prime_52077329 : Nat.Prime 52077329 := by
  apply nodeValid_prime [2, 19, 107, 1601] ⟨52077329, 3, [(2, 4), (19, 1), (107, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_107
    · exact prime_1601
  · decide +kernel

theorem prime_70470581 : Nat.Prime 70470581 := by
  apply nodeValid_prime [2, 5, 29, 121501] ⟨70470581, 3, [(2, 2), (5, 1), (29, 1), (121501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_121501
  · decide +kernel

theorem prime_118245349 : Nat.Prime 118245349 := by
  apply nodeValid_prime [2, 3, 13, 307, 823] ⟨118245349, 10, [(2, 2), (3, 2), (13, 1), (307, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_307
    · exact prime_823
  · decide +kernel

theorem prime_123083131 : Nat.Prime 123083131 := by
  apply nodeValid_prime [2, 3, 5, 47, 87293] ⟨123083131, 10, [(2, 1), (3, 1), (5, 1), (47, 1), (87293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_87293
  · decide +kernel

theorem prime_127294273 : Nat.Prime 127294273 := by
  apply nodeValid_prime [2, 3, 7, 131, 241] ⟨127294273, 5, [(2, 6), (3, 2), (7, 1), (131, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_131
    · exact prime_241
  · decide +kernel

theorem prime_151265617 : Nat.Prime 151265617 := by
  apply nodeValid_prime [2, 3, 31, 59, 1723] ⟨151265617, 5, [(2, 4), (3, 1), (31, 1), (59, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_59
    · exact prime_1723
  · decide +kernel

theorem prime_157932457 : Nat.Prime 157932457 := by
  apply nodeValid_prime [2, 3, 11, 598229] ⟨157932457, 10, [(2, 3), (3, 1), (11, 1), (598229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_598229
  · decide +kernel

theorem prime_199009793 : Nat.Prime 199009793 := by
  apply nodeValid_prime [2, 388691] ⟨199009793, 3, [(2, 9), (388691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_388691
  · decide +kernel

theorem prime_229120091 : Nat.Prime 229120091 := by
  apply nodeValid_prime [2, 5, 22912009] ⟨229120091, 2, [(2, 1), (5, 1), (22912009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22912009
  · decide +kernel

theorem prime_270843919 : Nat.Prime 270843919 := by
  apply nodeValid_prime [2, 3, 523, 86311] ⟨270843919, 3, [(2, 1), (3, 1), (523, 1), (86311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523
    · exact prime_86311
  · decide +kernel

theorem prime_468637391 : Nat.Prime 468637391 := by
  apply nodeValid_prime [2, 5, 13, 29, 197, 631] ⟨468637391, 19, [(2, 1), (5, 1), (13, 1), (29, 1), (197, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
    · exact prime_197
    · exact prime_631
  · decide +kernel

theorem prime_510359869 : Nat.Prime 510359869 := by
  apply nodeValid_prime [2, 3, 101, 140363] ⟨510359869, 2, [(2, 2), (3, 2), (101, 1), (140363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_140363
  · decide +kernel

theorem prime_578783213 : Nat.Prime 578783213 := by
  apply nodeValid_prime [2, 7, 139, 148711] ⟨578783213, 2, [(2, 2), (7, 1), (139, 1), (148711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_139
    · exact prime_148711
  · decide +kernel

theorem prime_773793197 : Nat.Prime 773793197 := by
  apply nodeValid_prime [2, 11, 29, 317, 1913] ⟨773793197, 2, [(2, 2), (11, 1), (29, 1), (317, 1), (1913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_317
    · exact prime_1913
  · decide +kernel

theorem prime_819867073 : Nat.Prime 819867073 := by
  apply nodeValid_prime [2, 3, 719, 5939] ⟨819867073, 15, [(2, 6), (3, 1), (719, 1), (5939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_719
    · exact prime_5939
  · decide +kernel

theorem prime_845646973 : Nat.Prime 845646973 := by
  apply nodeValid_prime [2, 3, 70470581] ⟨845646973, 5, [(2, 2), (3, 1), (70470581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_70470581
  · decide +kernel

theorem prime_1035587893 : Nat.Prime 1035587893 := by
  apply nodeValid_prime [2, 3, 2273, 37967] ⟨1035587893, 2, [(2, 2), (3, 1), (2273, 1), (37967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2273
    · exact prime_37967
  · decide +kernel

theorem prime_1077844849 : Nat.Prime 1077844849 := by
  apply nodeValid_prime [2, 3, 22455101] ⟨1077844849, 17, [(2, 4), (3, 1), (22455101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22455101
  · decide +kernel

theorem prime_1546472887 : Nat.Prime 1546472887 := by
  apply nodeValid_prime [2, 3, 7, 1459, 25237] ⟨1546472887, 3, [(2, 1), (3, 1), (7, 1), (1459, 1), (25237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1459
    · exact prime_25237
  · decide +kernel

theorem prime_2397457151 : Nat.Prime 2397457151 := by
  apply nodeValid_prime [2, 5, 11, 863, 5051] ⟨2397457151, 11, [(2, 1), (5, 2), (11, 1), (863, 1), (5051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_863
    · exact prime_5051
  · decide +kernel

theorem prime_2619433259 : Nat.Prime 2619433259 := by
  apply nodeValid_prime [2, 13, 601, 167633] ⟨2619433259, 2, [(2, 1), (13, 1), (601, 1), (167633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_601
    · exact prime_167633
  · decide +kernel

theorem prime_3197208809 : Nat.Prime 3197208809 := by
  apply nodeValid_prime [2, 31, 12891971] ⟨3197208809, 3, [(2, 3), (31, 1), (12891971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_12891971
  · decide +kernel

theorem prime_4794914303 : Nat.Prime 4794914303 := by
  apply nodeValid_prime [2, 2397457151] ⟨4794914303, 5, [(2, 1), (2397457151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2397457151
  · decide +kernel

theorem prime_7721695651 : Nat.Prime 7721695651 := by
  apply nodeValid_prime [2, 3, 5, 239, 215389] ⟨7721695651, 2, [(2, 1), (3, 1), (5, 2), (239, 1), (215389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239
    · exact prime_215389
  · decide +kernel

theorem prime_9637981183 : Nat.Prime 9637981183 := by
  apply nodeValid_prime [2, 3, 19831237] ⟨9637981183, 3, [(2, 1), (3, 5), (19831237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19831237
  · decide +kernel

theorem prime_15107664937 : Nat.Prime 15107664937 := by
  apply nodeValid_prime [2, 3, 7, 13, 1381, 5009] ⟨15107664937, 5, [(2, 3), (3, 1), (7, 1), (13, 1), (1381, 1), (5009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1381
    · exact prime_5009
  · decide +kernel

theorem prime_16716822613 : Nat.Prime 16716822613 := by
  apply nodeValid_prime [2, 3, 7, 199009793] ⟨16716822613, 2, [(2, 2), (3, 1), (7, 1), (199009793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199009793
  · decide +kernel

theorem prime_21685457681 : Nat.Prime 21685457681 := by
  apply nodeValid_prime [2, 5, 167, 1623163] ⟨21685457681, 6, [(2, 4), (5, 1), (167, 1), (1623163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_1623163
  · decide +kernel

theorem prime_21908797319 : Nat.Prime 21908797319 := by
  apply nodeValid_prime [2, 89, 123083131] ⟨21908797319, 13, [(2, 1), (89, 1), (123083131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_123083131
  · decide +kernel

theorem prime_22425127691 : Nat.Prime 22425127691 := by
  apply nodeValid_prime [2, 5, 7, 59, 73, 74381] ⟨22425127691, 17, [(2, 1), (5, 1), (7, 1), (59, 1), (73, 1), (74381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_73
    · exact prime_74381
  · decide +kernel

theorem prime_23301149323 : Nat.Prime 23301149323 := by
  apply nodeValid_prime [2, 3, 11, 1601, 20047] ⟨23301149323, 2, [(2, 1), (3, 1), (11, 2), (1601, 1), (20047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1601
    · exact prime_20047
  · decide +kernel

theorem prime_115995257023 : Nat.Prime 115995257023 := by
  apply nodeValid_prime [2, 3, 439, 44037683] ⟨115995257023, 3, [(2, 1), (3, 1), (439, 1), (44037683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_439
    · exact prime_44037683
  · decide +kernel

theorem prime_173483661277 : Nat.Prime 173483661277 := by
  apply nodeValid_prime [2, 3, 19831237] ⟨173483661277, 2, [(2, 2), (3, 7), (19831237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19831237
  · decide +kernel

theorem prime_350028706949 : Nat.Prime 350028706949 := by
  apply nodeValid_prime [2, 29, 71, 42499843] ⟨350028706949, 2, [(2, 2), (29, 1), (71, 1), (42499843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_71
    · exact prime_42499843
  · decide +kernel

theorem prime_692917718897 : Nat.Prime 692917718897 := by
  apply nodeValid_prime [2, 13, 601, 1307, 4241] ⟨692917718897, 3, [(2, 4), (13, 1), (601, 1), (1307, 1), (4241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_601
    · exact prime_1307
    · exact prime_4241
  · decide +kernel

theorem prime_692917745141 : Nat.Prime 692917745141 := by
  apply nodeValid_prime [2, 5, 293, 118245349] ⟨692917745141, 7, [(2, 2), (5, 1), (293, 1), (118245349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_293
    · exact prime_118245349
  · decide +kernel

theorem prime_692917745959 : Nat.Prime 692917745959 := by
  apply nodeValid_prime [2, 3, 25423, 1514197] ⟨692917745959, 3, [(2, 1), (3, 2), (25423, 1), (1514197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25423
    · exact prime_1514197
  · decide +kernel

theorem prime_693934645109 : Nat.Prime 693934645109 := by
  apply nodeValid_prime [2, 173483661277] ⟨693934645109, 2, [(2, 2), (173483661277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_173483661277
  · decide +kernel

theorem prime_693934645177 : Nat.Prime 693934645177 := by
  apply nodeValid_prime [2, 3, 9637981183] ⟨693934645177, 5, [(2, 3), (3, 2), (9637981183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9637981183
  · decide +kernel

theorem prime_693934645793 : Nat.Prime 693934645793 := by
  apply nodeValid_prime [2, 21685457681] ⟨693934645793, 3, [(2, 5), (21685457681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21685457681
  · decide +kernel

theorem prime_694952587103 : Nat.Prime 694952587103 := by
  apply nodeValid_prime [2, 23, 15107664937] ⟨694952587103, 5, [(2, 1), (23, 1), (15107664937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_15107664937
  · decide +kernel

theorem prime_694952608591 : Nat.Prime 694952608591 := by
  apply nodeValid_prime [2, 3, 5, 7721695651] ⟨694952608591, 6, [(2, 1), (3, 2), (5, 1), (7721695651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7721695651
  · decide +kernel

theorem prime_694952609053 : Nat.Prime 694952609053 := by
  apply nodeValid_prime [2, 3, 13, 19, 373, 628591] ⟨694952609053, 5, [(2, 2), (3, 1), (13, 1), (19, 1), (373, 1), (628591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_373
    · exact prime_628591
  · decide +kernel

theorem prime_695971539577 : Nat.Prime 695971539577 := by
  apply nodeValid_prime [2, 3, 17, 83, 2283551] ⟨695971539577, 7, [(2, 3), (3, 3), (17, 1), (83, 1), (2283551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_83
    · exact prime_2283551
  · decide +kernel

theorem prime_695971542107 : Nat.Prime 695971542107 := by
  apply nodeValid_prime [2, 71, 163, 919, 32719] ⟨695971542107, 2, [(2, 1), (71, 1), (163, 1), (919, 1), (32719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_163
    · exact prime_919
    · exact prime_32719
  · decide +kernel

theorem prime_695971542139 : Nat.Prime 695971542139 := by
  apply nodeValid_prime [2, 3, 115995257023] ⟨695971542139, 2, [(2, 1), (3, 1), (115995257023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115995257023
  · decide +kernel

theorem prime_696991505713 : Nat.Prime 696991505713 := by
  apply nodeValid_prime [2, 3, 17, 43, 19864099] ⟨696991505713, 7, [(2, 4), (3, 1), (17, 1), (43, 1), (19864099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_19864099
  · decide +kernel

theorem prime_696991519883 : Nat.Prime 696991519883 := by
  apply nodeValid_prime [2, 7, 47, 53, 487, 41039] ⟨696991519883, 2, [(2, 1), (7, 1), (47, 1), (53, 1), (487, 1), (41039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_53
    · exact prime_487
    · exact prime_41039
  · decide +kernel

theorem prime_696991520363 : Nat.Prime 696991520363 := by
  apply nodeValid_prime [2, 109, 3197208809] ⟨696991520363, 2, [(2, 1), (109, 1), (3197208809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_3197208809
  · decide +kernel

theorem prime_698012487041 : Nat.Prime 698012487041 := by
  apply nodeValid_prime [2, 5, 11, 31, 290761] ⟨698012487041, 15, [(2, 7), (5, 1), (11, 2), (31, 1), (290761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_290761
  · decide +kernel

theorem prime_698012554879 : Nat.Prime 698012554879 := by
  apply nodeValid_prime [2, 3, 67, 578783213] ⟨698012554879, 6, [(2, 1), (3, 2), (67, 1), (578783213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_578783213
  · decide +kernel

theorem prime_698012554949 : Nat.Prime 698012554949 := by
  apply nodeValid_prime [2, 19, 18587, 494129] ⟨698012554949, 3, [(2, 2), (19, 1), (18587, 1), (494129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_18587
    · exact prime_494129
  · decide +kernel

theorem prime_699034479691 : Nat.Prime 699034479691 := by
  apply nodeValid_prime [2, 3, 5, 23301149323] ⟨699034479691, 2, [(2, 1), (3, 1), (5, 1), (23301149323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23301149323
  · decide +kernel

theorem prime_699034482827 : Nat.Prime 699034482827 := by
  apply nodeValid_prime [2, 31, 24203, 465841] ⟨699034482827, 2, [(2, 1), (31, 1), (24203, 1), (465841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_24203
    · exact prime_465841
  · decide +kernel

theorem prime_699034484543 : Nat.Prime 699034484543 := by
  apply nodeValid_prime [2, 29, 104473, 115363] ⟨699034484543, 5, [(2, 1), (29, 1), (104473, 1), (115363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_104473
    · exact prime_115363
  · decide +kernel

theorem prime_700057413899 : Nat.Prime 700057413899 := by
  apply nodeValid_prime [2, 350028706949] ⟨700057413899, 2, [(2, 1), (350028706949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_350028706949
  · decide +kernel

theorem prime_700057415669 : Nat.Prime 700057415669 := by
  apply nodeValid_prime [2, 13, 1035587893] ⟨700057415669, 2, [(2, 2), (13, 2), (1035587893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1035587893
  · decide +kernel

theorem prime_700057488239 : Nat.Prime 700057488239 := by
  apply nodeValid_prime [2, 73, 4794914303] ⟨700057488239, 7, [(2, 1), (73, 1), (4794914303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_4794914303
  · decide +kernel

theorem prime_701081514209 : Nat.Prime 701081514209 := by
  apply nodeValid_prime [2, 21908797319] ⟨701081514209, 3, [(2, 5), (21908797319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21908797319
  · decide +kernel

theorem prime_701081536937 : Nat.Prime 701081536937 := by
  apply nodeValid_prime [2, 11, 17, 468637391] ⟨701081536937, 3, [(2, 3), (11, 1), (17, 1), (468637391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_468637391
  · decide +kernel

theorem prime_701081537119 : Nat.Prime 701081537119 := by
  apply nodeValid_prime [2, 3, 161507, 723479] ⟨701081537119, 3, [(2, 1), (3, 1), (161507, 1), (723479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_161507
    · exact prime_723479
  · decide +kernel

theorem prime_702106549579 : Nat.Prime 702106549579 := by
  apply nodeValid_prime [2, 3, 7, 107, 52077329] ⟨702106549579, 2, [(2, 1), (3, 2), (7, 1), (107, 1), (52077329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_52077329
  · decide +kernel

theorem prime_702106549747 : Nat.Prime 702106549747 := by
  apply nodeValid_prime [2, 3, 7, 16716822613] ⟨702106549747, 3, [(2, 1), (3, 1), (7, 1), (16716822613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_16716822613
  · decide +kernel

theorem prime_702106555009 : Nat.Prime 702106555009 := by
  apply nodeValid_prime [2, 3, 277, 6600731] ⟨702106555009, 13, [(2, 7), (3, 1), (277, 1), (6600731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_6600731
  · decide +kernel

theorem prime_703132570229 : Nat.Prime 703132570229 := by
  apply nodeValid_prime [2, 11, 13451, 1188037] ⟨703132570229, 2, [(2, 2), (11, 1), (13451, 1), (1188037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13451
    · exact prime_1188037
  · decide +kernel

theorem prime_703132570649 : Nat.Prime 703132570649 := by
  apply nodeValid_prime [2, 29, 2971, 1020109] ⟨703132570649, 3, [(2, 3), (29, 1), (2971, 1), (1020109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_2971
    · exact prime_1020109
  · decide +kernel

theorem prime_703132610779 : Nat.Prime 703132610779 := by
  apply nodeValid_prime [2, 3, 13, 229, 13121573] ⟨703132610779, 7, [(2, 1), (3, 2), (13, 1), (229, 1), (13121573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_229
    · exact prime_13121573
  · decide +kernel

theorem prime_704159645359 : Nat.Prime 704159645359 := by
  apply nodeValid_prime [2, 3, 13, 43, 47, 4466941] ⟨704159645359, 7, [(2, 1), (3, 1), (13, 1), (43, 1), (47, 1), (4466941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_47
    · exact prime_4466941
  · decide +kernel

theorem prime_704159645851 : Nat.Prime 704159645851 := by
  apply nodeValid_prime [2, 3, 5, 691, 2264543] ⟨704159645851, 2, [(2, 1), (3, 2), (5, 2), (691, 1), (2264543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_691
    · exact prime_2264543
  · decide +kernel

theorem prime_704159676637 : Nat.Prime 704159676637 := by
  apply nodeValid_prime [2, 3, 13, 44917, 100493] ⟨704159676637, 2, [(2, 2), (3, 1), (13, 1), (44917, 1), (100493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_44917
    · exact prime_100493
  · decide +kernel

theorem prime_705187763359 : Nat.Prime 705187763359 := by
  apply nodeValid_prime [2, 3, 13, 127, 173, 411491] ⟨705187763359, 23, [(2, 1), (3, 1), (13, 1), (127, 1), (173, 1), (411491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_127
    · exact prime_173
    · exact prime_411491
  · decide +kernel

theorem prime_705187794977 : Nat.Prime 705187794977 := by
  apply nodeValid_prime [2, 7, 19, 23, 101, 71327] ⟨705187794977, 5, [(2, 5), (7, 1), (19, 1), (23, 1), (101, 1), (71327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_101
    · exact prime_71327
  · decide +kernel

theorem prime_705187795177 : Nat.Prime 705187795177 := by
  apply nodeValid_prime [2, 3, 8269, 394819] ⟨705187795177, 5, [(2, 3), (3, 3), (8269, 1), (394819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8269
    · exact prime_394819
  · decide +kernel

theorem prime_706216866793 : Nat.Prime 706216866793 := by
  apply nodeValid_prime [2, 3, 10753, 2736511] ⟨706216866793, 15, [(2, 3), (3, 1), (10753, 1), (2736511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10753
    · exact prime_2736511
  · decide +kernel

theorem prime_706216893329 : Nat.Prime 706216893329 := by
  apply nodeValid_prime [2, 6113, 7220441] ⟨706216893329, 3, [(2, 4), (6113, 1), (7220441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6113
    · exact prime_7220441
  · decide +kernel

theorem prime_706216895693 : Nat.Prime 706216895693 := by
  apply nodeValid_prime [2, 7, 11, 29, 101, 111833] ⟨706216895693, 2, [(2, 2), (7, 2), (11, 1), (29, 1), (101, 1), (111833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_101
    · exact prime_111833
  · decide +kernel

theorem prime_707246979931 : Nat.Prime 707246979931 := by
  apply nodeValid_prime [2, 3, 5, 2619433259] ⟨707246979931, 2, [(2, 1), (3, 3), (5, 1), (2619433259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2619433259
  · decide +kernel

theorem prime_707246980789 : Nat.Prime 707246980789 := by
  apply nodeValid_prime [2, 3, 463, 127294273] ⟨707246980789, 2, [(2, 2), (3, 1), (463, 1), (127294273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
    · exact prime_127294273
  · decide +kernel

theorem prime_707246982059 : Nat.Prime 707246982059 := by
  apply nodeValid_prime [2, 457, 773793197] ⟨707246982059, 2, [(2, 1), (457, 1), (773793197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_773793197
  · decide +kernel

theorem prime_708278109373 : Nat.Prime 708278109373 := by
  apply nodeValid_prime [2, 3, 389, 2141, 23623] ⟨708278109373, 2, [(2, 2), (3, 2), (389, 1), (2141, 1), (23623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_2141
    · exact prime_23623
  · decide +kernel

theorem prime_708278176201 : Nat.Prime 708278176201 := by
  apply nodeValid_prime [2, 3, 5, 7, 229, 736409] ⟨708278176201, 13, [(2, 3), (3, 1), (5, 2), (7, 1), (229, 1), (736409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_229
    · exact prime_736409
  · decide +kernel

theorem prime_708278176451 : Nat.Prime 708278176451 := by
  apply nodeValid_prime [2, 5, 13, 103, 151, 70061] ⟨708278176451, 2, [(2, 1), (5, 2), (13, 1), (103, 1), (151, 1), (70061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_103
    · exact prime_151
    · exact prime_70061
  · decide +kernel

theorem prime_709310254699 : Nat.Prime 709310254699 := by
  apply nodeValid_prime [2, 3, 31, 2083, 203419] ⟨709310254699, 2, [(2, 1), (3, 3), (31, 1), (2083, 1), (203419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_2083
    · exact prime_203419
  · decide +kernel

theorem prime_709310279761 : Nat.Prime 709310279761 := by
  apply nodeValid_prime [2, 3, 5, 47, 3797, 16561] ⟨709310279761, 7, [(2, 4), (3, 1), (5, 1), (47, 1), (3797, 1), (16561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_3797
    · exact prime_16561
  · decide +kernel

theorem prime_709310280251 : Nat.Prime 709310280251 := by
  apply nodeValid_prime [2, 5, 11, 13, 283, 5393] ⟨709310280251, 2, [(2, 1), (5, 3), (11, 1), (13, 2), (283, 1), (5393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_283
    · exact prime_5393
  · decide +kernel

theorem prime_710343418397 : Nat.Prime 710343418397 := by
  apply nodeValid_prime [2, 23, 29021, 266053] ⟨710343418397, 2, [(2, 2), (23, 1), (29021, 1), (266053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_29021
    · exact prime_266053
  · decide +kernel

theorem prime_710343457321 : Nat.Prime 710343457321 := by
  apply nodeValid_prime [2, 3, 5, 7, 845646973] ⟨710343457321, 19, [(2, 3), (3, 1), (5, 1), (7, 1), (845646973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_845646973
  · decide +kernel

theorem prime_710343458537 : Nat.Prime 710343458537 := by
  apply nodeValid_prime [2, 2707, 32801231] ⟨710343458537, 3, [(2, 3), (2707, 1), (32801231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2707
    · exact prime_32801231
  · decide +kernel

theorem prime_711377527373 : Nat.Prime 711377527373 := by
  apply nodeValid_prime [2, 8243, 21575201] ⟨711377527373, 2, [(2, 2), (8243, 1), (21575201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8243
    · exact prime_21575201
  · decide +kernel

theorem prime_711377528021 : Nat.Prime 711377528021 := by
  apply nodeValid_prime [2, 5, 23, 1546472887] ⟨711377528021, 2, [(2, 2), (5, 1), (23, 1), (1546472887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1546472887
  · decide +kernel

theorem prime_711377600341 : Nat.Prime 711377600341 := by
  apply nodeValid_prime [2, 3, 5, 11, 1077844849] ⟨711377600341, 14, [(2, 2), (3, 1), (5, 1), (11, 1), (1077844849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1077844849
  · decide +kernel

theorem prime_712412799691 : Nat.Prime 712412799691 := by
  apply nodeValid_prime [2, 3, 5, 19, 29, 43098173] ⟨712412799691, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (29, 1), (43098173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_43098173
  · decide +kernel

theorem prime_712412821313 : Nat.Prime 712412821313 := by
  apply nodeValid_prime [2, 19, 31, 37, 73, 6997] ⟨712412821313, 3, [(2, 6), (19, 1), (31, 1), (37, 1), (73, 1), (6997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_37
    · exact prime_73
    · exact prime_6997
  · decide +kernel

theorem prime_712412821399 : Nat.Prime 712412821399 := by
  apply nodeValid_prime [2, 3, 397, 1381, 216569] ⟨712412821399, 3, [(2, 1), (3, 1), (397, 1), (1381, 1), (216569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_1381
    · exact prime_216569
  · decide +kernel

theorem prime_713449018021 : Nat.Prime 713449018021 := by
  apply nodeValid_prime [2, 3, 5, 719, 1709, 9677] ⟨713449018021, 2, [(2, 2), (3, 1), (5, 1), (719, 1), (1709, 1), (9677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_719
    · exact prime_1709
    · exact prime_9677
  · decide +kernel

theorem prime_713449030309 : Nat.Prime 713449030309 := by
  apply nodeValid_prime [2, 3, 7, 163, 1231, 6047] ⟨713449030309, 2, [(2, 2), (3, 1), (7, 2), (163, 1), (1231, 1), (6047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_163
    · exact prime_1231
    · exact prime_6047
  · decide +kernel

theorem prime_713449031023 : Nat.Prime 713449031023 := by
  apply nodeValid_prime [2, 3, 7, 13, 59, 2460797] ⟨713449031023, 17, [(2, 1), (3, 3), (7, 1), (13, 1), (59, 1), (2460797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_59
    · exact prime_2460797
  · decide +kernel

theorem prime_714486258323 : Nat.Prime 714486258323 := by
  apply nodeValid_prime [2, 1319, 270843919] ⟨714486258323, 2, [(2, 1), (1319, 1), (270843919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1319
    · exact prime_270843919
  · decide +kernel

theorem prime_714486434369 : Nat.Prime 714486434369 := by
  apply nodeValid_prime [2, 7, 617, 1579, 1637] ⟨714486434369, 3, [(2, 6), (7, 1), (617, 1), (1579, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_617
    · exact prime_1579
    · exact prime_1637
  · decide +kernel

theorem prime_714486435469 : Nat.Prime 714486435469 := by
  apply nodeValid_prime [2, 3, 13, 29, 157932457] ⟨714486435469, 18, [(2, 2), (3, 1), (13, 1), (29, 1), (157932457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_157932457
  · decide +kernel

theorem prime_715524526147 : Nat.Prime 715524526147 := by
  apply nodeValid_prime [2, 3, 109, 12491, 87589] ⟨715524526147, 5, [(2, 1), (3, 1), (109, 1), (12491, 1), (87589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_12491
    · exact prime_87589
  · decide +kernel

theorem prime_715524536339 : Nat.Prime 715524536339 := by
  apply nodeValid_prime [2, 701, 510359869] ⟨715524536339, 2, [(2, 1), (701, 1), (510359869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_701
    · exact prime_510359869
  · decide +kernel

theorem prime_715524536399 : Nat.Prime 715524536399 := by
  apply nodeValid_prime [2, 7, 31, 2297, 717751] ⟨715524536399, 7, [(2, 1), (7, 1), (31, 1), (2297, 1), (717751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_2297
    · exact prime_717751
  · decide +kernel

theorem prime_716563814633 : Nat.Prime 716563814633 := by
  apply nodeValid_prime [2, 613, 1511, 96703] ⟨716563814633, 3, [(2, 3), (613, 1), (1511, 1), (96703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_613
    · exact prime_1511
    · exact prime_96703
  · decide +kernel

theorem prime_716563820933 : Nat.Prime 716563820933 := by
  apply nodeValid_prime [2, 17, 3083, 11827] ⟨716563820933, 2, [(2, 2), (17, 3), (3083, 1), (11827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3083
    · exact prime_11827
  · decide +kernel

theorem prime_716563821803 : Nat.Prime 716563821803 := by
  apply nodeValid_prime [2, 19, 23, 819867073] ⟨716563821803, 2, [(2, 1), (19, 1), (23, 1), (819867073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_819867073
  · decide +kernel

theorem prime_717604086113 : Nat.Prime 717604086113 := by
  apply nodeValid_prime [2, 22425127691] ⟨717604086113, 3, [(2, 5), (22425127691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22425127691
  · decide +kernel

theorem prime_717604087049 : Nat.Prime 717604087049 := by
  apply nodeValid_prime [2, 593, 151265617] ⟨717604087049, 3, [(2, 3), (593, 1), (151265617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_593
    · exact prime_151265617
  · decide +kernel

theorem prime_717604125013 : Nat.Prime 717604125013 := by
  apply nodeValid_prime [2, 3, 29, 229120091] ⟨717604125013, 2, [(2, 2), (3, 3), (29, 1), (229120091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_229120091
  · decide +kernel

end Sude.Lucas.Generated
