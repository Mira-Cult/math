import Sude.LucasCertificate
import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
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
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0146
import Sude.GeneratedTwinBase.M000

/-! Generated Lucas nodes for the FT base; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_27997 : Nat.Prime 27997 := by
  apply nodeValid_prime [2, 3, 2333] ⟨27997, 5, [(2, 2), (3, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2333
  · decide +kernel

theorem prime_28001 : Nat.Prime 28001 := by
  apply nodeValid_prime [2, 5, 7] ⟨28001, 3, [(2, 5), (5, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_28031 : Nat.Prime 28031 := by
  apply nodeValid_prime [2, 5, 2803] ⟨28031, 19, [(2, 1), (5, 1), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2803
  · decide +kernel

theorem prime_28057 : Nat.Prime 28057 := by
  apply nodeValid_prime [2, 3, 7, 167] ⟨28057, 5, [(2, 3), (3, 1), (7, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_167
  · decide +kernel

theorem prime_28081 : Nat.Prime 28081 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨28081, 19, [(2, 4), (3, 3), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_28087 : Nat.Prime 28087 := by
  apply nodeValid_prime [2, 3, 31, 151] ⟨28087, 3, [(2, 1), (3, 1), (31, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_151
  · decide +kernel

theorem prime_28099 : Nat.Prime 28099 := by
  apply nodeValid_prime [2, 3, 7, 223] ⟨28099, 2, [(2, 1), (3, 2), (7, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_223
  · decide +kernel

theorem prime_28111 : Nat.Prime 28111 := by
  apply nodeValid_prime [2, 3, 5, 937] ⟨28111, 3, [(2, 1), (3, 1), (5, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_937
  · decide +kernel

theorem prime_28183 : Nat.Prime 28183 := by
  apply nodeValid_prime [2, 3, 7, 11, 61] ⟨28183, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_28201 : Nat.Prime 28201 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨28201, 11, [(2, 3), (3, 1), (5, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_28211 : Nat.Prime 28211 := by
  apply nodeValid_prime [2, 5, 7, 13, 31] ⟨28211, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_28289 : Nat.Prime 28289 := by
  apply nodeValid_prime [2, 13, 17] ⟨28289, 6, [(2, 7), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_28351 : Nat.Prime 28351 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨28351, 6, [(2, 1), (3, 4), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_28429 : Nat.Prime 28429 := by
  apply nodeValid_prime [2, 3, 23, 103] ⟨28429, 2, [(2, 2), (3, 1), (23, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_103
  · decide +kernel

theorem prime_28433 : Nat.Prime 28433 := by
  apply nodeValid_prime [2, 1777] ⟨28433, 3, [(2, 4), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1777
  · decide +kernel

theorem prime_28477 : Nat.Prime 28477 := by
  apply nodeValid_prime [2, 3, 7, 113] ⟨28477, 2, [(2, 2), (3, 2), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_28493 : Nat.Prime 28493 := by
  apply nodeValid_prime [2, 17, 419] ⟨28493, 2, [(2, 2), (17, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_419
  · decide +kernel

theorem prime_28549 : Nat.Prime 28549 := by
  apply nodeValid_prime [2, 3, 13, 61] ⟨28549, 2, [(2, 2), (3, 2), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_28559 : Nat.Prime 28559 := by
  apply nodeValid_prime [2, 109, 131] ⟨28559, 11, [(2, 1), (109, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_131
  · decide +kernel

theorem prime_28591 : Nat.Prime 28591 := by
  apply nodeValid_prime [2, 3, 5, 953] ⟨28591, 3, [(2, 1), (3, 1), (5, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_953
  · decide +kernel

theorem prime_28603 : Nat.Prime 28603 := by
  apply nodeValid_prime [2, 3, 7, 227] ⟨28603, 2, [(2, 1), (3, 2), (7, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_227
  · decide +kernel

theorem prime_28619 : Nat.Prime 28619 := by
  apply nodeValid_prime [2, 41, 349] ⟨28619, 2, [(2, 1), (41, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_349
  · decide +kernel

theorem prime_28663 : Nat.Prime 28663 := by
  apply nodeValid_prime [2, 3, 17, 281] ⟨28663, 3, [(2, 1), (3, 1), (17, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_281
  · decide +kernel

theorem prime_28669 : Nat.Prime 28669 := by
  apply nodeValid_prime [2, 3, 2389] ⟨28669, 6, [(2, 2), (3, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2389
  · decide +kernel

theorem prime_28703 : Nat.Prime 28703 := by
  apply nodeValid_prime [2, 113, 127] ⟨28703, 5, [(2, 1), (113, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_127
  · decide +kernel

theorem prime_28711 : Nat.Prime 28711 := by
  apply nodeValid_prime [2, 3, 5, 11, 29] ⟨28711, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_28751 : Nat.Prime 28751 := by
  apply nodeValid_prime [2, 5, 23] ⟨28751, 14, [(2, 1), (5, 4), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_28753 : Nat.Prime 28753 := by
  apply nodeValid_prime [2, 3, 599] ⟨28753, 10, [(2, 4), (3, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_599
  · decide +kernel

theorem prime_28789 : Nat.Prime 28789 := by
  apply nodeValid_prime [2, 3, 2399] ⟨28789, 7, [(2, 2), (3, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2399
  · decide +kernel

theorem prime_28817 : Nat.Prime 28817 := by
  apply nodeValid_prime [2, 1801] ⟨28817, 3, [(2, 4), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1801
  · decide +kernel

theorem prime_28859 : Nat.Prime 28859 := by
  apply nodeValid_prime [2, 47, 307] ⟨28859, 2, [(2, 1), (47, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_307
  · decide +kernel

theorem prime_28871 : Nat.Prime 28871 := by
  apply nodeValid_prime [2, 5, 2887] ⟨28871, 13, [(2, 1), (5, 1), (2887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2887
  · decide +kernel

theorem prime_28909 : Nat.Prime 28909 := by
  apply nodeValid_prime [2, 3, 11, 73] ⟨28909, 2, [(2, 2), (3, 2), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_28927 : Nat.Prime 28927 := by
  apply nodeValid_prime [2, 3, 1607] ⟨28927, 3, [(2, 1), (3, 2), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1607
  · decide +kernel

theorem prime_28949 : Nat.Prime 28949 := by
  apply nodeValid_prime [2, 7237] ⟨28949, 2, [(2, 2), (7237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7237
  · decide +kernel

theorem prime_28979 : Nat.Prime 28979 := by
  apply nodeValid_prime [2, 14489] ⟨28979, 2, [(2, 1), (14489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14489
  · decide +kernel

theorem prime_29009 : Nat.Prime 29009 := by
  apply nodeValid_prime [2, 7, 37] ⟨29009, 3, [(2, 4), (7, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_29023 : Nat.Prime 29023 := by
  apply nodeValid_prime [2, 3, 7, 691] ⟨29023, 3, [(2, 1), (3, 1), (7, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_691
  · decide +kernel

theorem prime_29033 : Nat.Prime 29033 := by
  apply nodeValid_prime [2, 19, 191] ⟨29033, 3, [(2, 3), (19, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_191
  · decide +kernel

theorem prime_29059 : Nat.Prime 29059 := by
  apply nodeValid_prime [2, 3, 29, 167] ⟨29059, 2, [(2, 1), (3, 1), (29, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_167
  · decide +kernel

theorem prime_29101 : Nat.Prime 29101 := by
  apply nodeValid_prime [2, 3, 5, 97] ⟨29101, 2, [(2, 2), (3, 1), (5, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_29123 : Nat.Prime 29123 := by
  apply nodeValid_prime [2, 14561] ⟨29123, 2, [(2, 1), (14561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14561
  · decide +kernel

theorem prime_29131 : Nat.Prime 29131 := by
  apply nodeValid_prime [2, 3, 5, 971] ⟨29131, 2, [(2, 1), (3, 1), (5, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_971
  · decide +kernel

theorem prime_29153 : Nat.Prime 29153 := by
  apply nodeValid_prime [2, 911] ⟨29153, 3, [(2, 5), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_911
  · decide +kernel

theorem prime_29167 : Nat.Prime 29167 := by
  apply nodeValid_prime [2, 3, 4861] ⟨29167, 3, [(2, 1), (3, 1), (4861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4861
  · decide +kernel

theorem prime_29191 : Nat.Prime 29191 := by
  apply nodeValid_prime [2, 3, 5, 7, 139] ⟨29191, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_139
  · decide +kernel

theorem prime_29207 : Nat.Prime 29207 := by
  apply nodeValid_prime [2, 17, 859] ⟨29207, 5, [(2, 1), (17, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_859
  · decide +kernel

theorem prime_29209 : Nat.Prime 29209 := by
  apply nodeValid_prime [2, 3, 1217] ⟨29209, 7, [(2, 3), (3, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1217
  · decide +kernel

theorem prime_29251 : Nat.Prime 29251 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨29251, 2, [(2, 1), (3, 2), (5, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_29269 : Nat.Prime 29269 := by
  apply nodeValid_prime [2, 3, 271] ⟨29269, 6, [(2, 2), (3, 3), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
  · decide +kernel

theorem prime_29297 : Nat.Prime 29297 := by
  apply nodeValid_prime [2, 1831] ⟨29297, 3, [(2, 4), (1831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1831
  · decide +kernel

theorem prime_29327 : Nat.Prime 29327 := by
  apply nodeValid_prime [2, 11, 31, 43] ⟨29327, 5, [(2, 1), (11, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_29333 : Nat.Prime 29333 := by
  apply nodeValid_prime [2, 7333] ⟨29333, 2, [(2, 2), (7333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7333
  · decide +kernel

theorem prime_29363 : Nat.Prime 29363 := by
  apply nodeValid_prime [2, 53, 277] ⟨29363, 2, [(2, 1), (53, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_277
  · decide +kernel

theorem prime_29399 : Nat.Prime 29399 := by
  apply nodeValid_prime [2, 14699] ⟨29399, 13, [(2, 1), (14699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14699
  · decide +kernel

theorem prime_29401 : Nat.Prime 29401 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨29401, 13, [(2, 3), (3, 1), (5, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_29437 : Nat.Prime 29437 := by
  apply nodeValid_prime [2, 3, 11, 223] ⟨29437, 2, [(2, 2), (3, 1), (11, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_223
  · decide +kernel

theorem prime_29501 : Nat.Prime 29501 := by
  apply nodeValid_prime [2, 5, 59] ⟨29501, 2, [(2, 2), (5, 3), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
  · decide +kernel

theorem prime_29531 : Nat.Prime 29531 := by
  apply nodeValid_prime [2, 5, 2953] ⟨29531, 2, [(2, 1), (5, 1), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2953
  · decide +kernel

theorem prime_29537 : Nat.Prime 29537 := by
  apply nodeValid_prime [2, 13, 71] ⟨29537, 3, [(2, 5), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_29567 : Nat.Prime 29567 := by
  apply nodeValid_prime [2, 14783] ⟨29567, 5, [(2, 1), (14783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14783
  · decide +kernel

theorem prime_29581 : Nat.Prime 29581 := by
  apply nodeValid_prime [2, 3, 5, 17, 29] ⟨29581, 10, [(2, 2), (3, 1), (5, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_29599 : Nat.Prime 29599 := by
  apply nodeValid_prime [2, 3, 4933] ⟨29599, 13, [(2, 1), (3, 1), (4933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4933
  · decide +kernel

theorem prime_29611 : Nat.Prime 29611 := by
  apply nodeValid_prime [2, 3, 5, 7, 47] ⟨29611, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_29629 : Nat.Prime 29629 := by
  apply nodeValid_prime [2, 3, 823] ⟨29629, 7, [(2, 2), (3, 2), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_823
  · decide +kernel

theorem prime_29633 : Nat.Prime 29633 := by
  apply nodeValid_prime [2, 463] ⟨29633, 3, [(2, 6), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_463
  · decide +kernel

theorem prime_29669 : Nat.Prime 29669 := by
  apply nodeValid_prime [2, 7417] ⟨29669, 2, [(2, 2), (7417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7417
  · decide +kernel

theorem prime_29671 : Nat.Prime 29671 := by
  apply nodeValid_prime [2, 3, 5, 23, 43] ⟨29671, 6, [(2, 1), (3, 1), (5, 1), (23, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_43
  · decide +kernel

theorem prime_29683 : Nat.Prime 29683 := by
  apply nodeValid_prime [2, 3, 17, 97] ⟨29683, 11, [(2, 1), (3, 2), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_29717 : Nat.Prime 29717 := by
  apply nodeValid_prime [2, 17, 19, 23] ⟨29717, 2, [(2, 2), (17, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_29753 : Nat.Prime 29753 := by
  apply nodeValid_prime [2, 3719] ⟨29753, 3, [(2, 3), (3719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3719
  · decide +kernel

theorem prime_29759 : Nat.Prime 29759 := by
  apply nodeValid_prime [2, 14879] ⟨29759, 7, [(2, 1), (14879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14879
  · decide +kernel

theorem prime_29819 : Nat.Prime 29819 := by
  apply nodeValid_prime [2, 17, 877] ⟨29819, 6, [(2, 1), (17, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_877
  · decide +kernel

theorem prime_29837 : Nat.Prime 29837 := by
  apply nodeValid_prime [2, 7459] ⟨29837, 2, [(2, 2), (7459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7459
  · decide +kernel

theorem prime_29867 : Nat.Prime 29867 := by
  apply nodeValid_prime [2, 109, 137] ⟨29867, 2, [(2, 1), (109, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_137
  · decide +kernel

theorem prime_29879 : Nat.Prime 29879 := by
  apply nodeValid_prime [2, 14939] ⟨29879, 11, [(2, 1), (14939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14939
  · decide +kernel

theorem prime_29917 : Nat.Prime 29917 := by
  apply nodeValid_prime [2, 3, 277] ⟨29917, 2, [(2, 2), (3, 3), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
  · decide +kernel

theorem prime_29921 : Nat.Prime 29921 := by
  apply nodeValid_prime [2, 5, 11, 17] ⟨29921, 3, [(2, 5), (5, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_29927 : Nat.Prime 29927 := by
  apply nodeValid_prime [2, 13, 1151] ⟨29927, 5, [(2, 1), (13, 1), (1151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1151
  · decide +kernel

theorem prime_29959 : Nat.Prime 29959 := by
  apply nodeValid_prime [2, 3, 4993] ⟨29959, 6, [(2, 1), (3, 1), (4993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4993
  · decide +kernel

theorem prime_30011 : Nat.Prime 30011 := by
  apply nodeValid_prime [2, 5, 3001] ⟨30011, 2, [(2, 1), (5, 1), (3001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3001
  · decide +kernel

theorem prime_30013 : Nat.Prime 30013 := by
  apply nodeValid_prime [2, 3, 41, 61] ⟨30013, 2, [(2, 2), (3, 1), (41, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_61
  · decide +kernel

theorem prime_30029 : Nat.Prime 30029 := by
  apply nodeValid_prime [2, 7507] ⟨30029, 2, [(2, 2), (7507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7507
  · decide +kernel

theorem prime_30047 : Nat.Prime 30047 := by
  apply nodeValid_prime [2, 83, 181] ⟨30047, 5, [(2, 1), (83, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_181
  · decide +kernel

theorem prime_30089 : Nat.Prime 30089 := by
  apply nodeValid_prime [2, 3761] ⟨30089, 3, [(2, 3), (3761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3761
  · decide +kernel

theorem prime_30097 : Nat.Prime 30097 := by
  apply nodeValid_prime [2, 3, 11, 19] ⟨30097, 10, [(2, 4), (3, 2), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_30119 : Nat.Prime 30119 := by
  apply nodeValid_prime [2, 11, 37] ⟨30119, 11, [(2, 1), (11, 1), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_30133 : Nat.Prime 30133 := by
  apply nodeValid_prime [2, 3, 31] ⟨30133, 5, [(2, 2), (3, 5), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_30137 : Nat.Prime 30137 := by
  apply nodeValid_prime [2, 3767] ⟨30137, 3, [(2, 3), (3767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3767
  · decide +kernel

theorem prime_30187 : Nat.Prime 30187 := by
  apply nodeValid_prime [2, 3, 13, 43] ⟨30187, 5, [(2, 1), (3, 3), (13, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
  · decide +kernel

theorem prime_30203 : Nat.Prime 30203 := by
  apply nodeValid_prime [2, 15101] ⟨30203, 2, [(2, 1), (15101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15101
  · decide +kernel

theorem prime_30259 : Nat.Prime 30259 := by
  apply nodeValid_prime [2, 3, 41] ⟨30259, 3, [(2, 1), (3, 2), (41, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_30271 : Nat.Prime 30271 := by
  apply nodeValid_prime [2, 3, 5, 1009] ⟨30271, 3, [(2, 1), (3, 1), (5, 1), (1009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1009
  · decide +kernel

theorem prime_30341 : Nat.Prime 30341 := by
  apply nodeValid_prime [2, 5, 37, 41] ⟨30341, 2, [(2, 2), (5, 1), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_30347 : Nat.Prime 30347 := by
  apply nodeValid_prime [2, 15173] ⟨30347, 2, [(2, 1), (15173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15173
  · decide +kernel

theorem prime_30367 : Nat.Prime 30367 := by
  apply nodeValid_prime [2, 3, 7, 241] ⟨30367, 5, [(2, 1), (3, 2), (7, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_241
  · decide +kernel

theorem prime_30403 : Nat.Prime 30403 := by
  apply nodeValid_prime [2, 3, 563] ⟨30403, 5, [(2, 1), (3, 3), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_563
  · decide +kernel

theorem prime_30427 : Nat.Prime 30427 := by
  apply nodeValid_prime [2, 3, 11, 461] ⟨30427, 5, [(2, 1), (3, 1), (11, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_461
  · decide +kernel

theorem prime_30431 : Nat.Prime 30431 := by
  apply nodeValid_prime [2, 5, 17, 179] ⟨30431, 11, [(2, 1), (5, 1), (17, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_179
  · decide +kernel

theorem prime_30467 : Nat.Prime 30467 := by
  apply nodeValid_prime [2, 15233] ⟨30467, 2, [(2, 1), (15233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15233
  · decide +kernel

theorem prime_30493 : Nat.Prime 30493 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨30493, 6, [(2, 2), (3, 2), (7, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_30509 : Nat.Prime 30509 := by
  apply nodeValid_prime [2, 29, 263] ⟨30509, 2, [(2, 2), (29, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_263
  · decide +kernel

theorem prime_30529 : Nat.Prime 30529 := by
  apply nodeValid_prime [2, 3, 53] ⟨30529, 13, [(2, 6), (3, 2), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
  · decide +kernel

theorem prime_30557 : Nat.Prime 30557 := by
  apply nodeValid_prime [2, 7639] ⟨30557, 2, [(2, 2), (7639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7639
  · decide +kernel

theorem prime_30559 : Nat.Prime 30559 := by
  apply nodeValid_prime [2, 3, 11, 463] ⟨30559, 7, [(2, 1), (3, 1), (11, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_463
  · decide +kernel

theorem prime_30577 : Nat.Prime 30577 := by
  apply nodeValid_prime [2, 3, 7, 13] ⟨30577, 5, [(2, 4), (3, 1), (7, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_30637 : Nat.Prime 30637 := by
  apply nodeValid_prime [2, 3, 23, 37] ⟨30637, 2, [(2, 2), (3, 2), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_30643 : Nat.Prime 30643 := by
  apply nodeValid_prime [2, 3, 5107] ⟨30643, 2, [(2, 1), (3, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5107
  · decide +kernel

theorem prime_30677 : Nat.Prime 30677 := by
  apply nodeValid_prime [2, 7669] ⟨30677, 2, [(2, 2), (7669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7669
  · decide +kernel

theorem prime_30697 : Nat.Prime 30697 := by
  apply nodeValid_prime [2, 3, 1279] ⟨30697, 10, [(2, 3), (3, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
  · decide +kernel

theorem prime_30707 : Nat.Prime 30707 := by
  apply nodeValid_prime [2, 13, 1181] ⟨30707, 2, [(2, 1), (13, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1181
  · decide +kernel

theorem prime_30713 : Nat.Prime 30713 := by
  apply nodeValid_prime [2, 11, 349] ⟨30713, 3, [(2, 3), (11, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_349
  · decide +kernel

theorem prime_30803 : Nat.Prime 30803 := by
  apply nodeValid_prime [2, 15401] ⟨30803, 2, [(2, 1), (15401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15401
  · decide +kernel

theorem prime_30809 : Nat.Prime 30809 := by
  apply nodeValid_prime [2, 3851] ⟨30809, 3, [(2, 3), (3851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3851
  · decide +kernel

theorem prime_30829 : Nat.Prime 30829 := by
  apply nodeValid_prime [2, 3, 7, 367] ⟨30829, 2, [(2, 2), (3, 1), (7, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_367
  · decide +kernel

theorem prime_30839 : Nat.Prime 30839 := by
  apply nodeValid_prime [2, 17, 907] ⟨30839, 7, [(2, 1), (17, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_907
  · decide +kernel

theorem prime_30853 : Nat.Prime 30853 := by
  apply nodeValid_prime [2, 3, 857] ⟨30853, 2, [(2, 2), (3, 2), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_857
  · decide +kernel

theorem prime_30859 : Nat.Prime 30859 := by
  apply nodeValid_prime [2, 3, 37, 139] ⟨30859, 2, [(2, 1), (3, 1), (37, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_139
  · decide +kernel

theorem prime_30871 : Nat.Prime 30871 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨30871, 3, [(2, 1), (3, 2), (5, 1), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_30893 : Nat.Prime 30893 := by
  apply nodeValid_prime [2, 7723] ⟨30893, 2, [(2, 2), (7723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7723
  · decide +kernel

theorem prime_30911 : Nat.Prime 30911 := by
  apply nodeValid_prime [2, 5, 11, 281] ⟨30911, 17, [(2, 1), (5, 1), (11, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_281
  · decide +kernel

theorem prime_30941 : Nat.Prime 30941 := by
  apply nodeValid_prime [2, 5, 7, 13, 17] ⟨30941, 2, [(2, 2), (5, 1), (7, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_30949 : Nat.Prime 30949 := by
  apply nodeValid_prime [2, 3, 2579] ⟨30949, 10, [(2, 2), (3, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2579
  · decide +kernel

theorem prime_30977 : Nat.Prime 30977 := by
  apply nodeValid_prime [2, 11] ⟨30977, 3, [(2, 8), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel

theorem prime_31013 : Nat.Prime 31013 := by
  apply nodeValid_prime [2, 7753] ⟨31013, 2, [(2, 2), (7753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7753
  · decide +kernel

theorem prime_31039 : Nat.Prime 31039 := by
  apply nodeValid_prime [2, 3, 7, 739] ⟨31039, 7, [(2, 1), (3, 1), (7, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_739
  · decide +kernel

theorem prime_31051 : Nat.Prime 31051 := by
  apply nodeValid_prime [2, 3, 5, 23] ⟨31051, 11, [(2, 1), (3, 3), (5, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel

theorem prime_31063 : Nat.Prime 31063 := by
  apply nodeValid_prime [2, 3, 31, 167] ⟨31063, 3, [(2, 1), (3, 1), (31, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_167
  · decide +kernel

theorem prime_31081 : Nat.Prime 31081 := by
  apply nodeValid_prime [2, 3, 5, 7, 37] ⟨31081, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_31091 : Nat.Prime 31091 := by
  apply nodeValid_prime [2, 5, 3109] ⟨31091, 2, [(2, 1), (5, 1), (3109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3109
  · decide +kernel

theorem prime_31121 : Nat.Prime 31121 := by
  apply nodeValid_prime [2, 5, 389] ⟨31121, 3, [(2, 4), (5, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_389
  · decide +kernel

theorem prime_31139 : Nat.Prime 31139 := by
  apply nodeValid_prime [2, 15569] ⟨31139, 2, [(2, 1), (15569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15569
  · decide +kernel

theorem prime_31151 : Nat.Prime 31151 := by
  apply nodeValid_prime [2, 5, 7, 89] ⟨31151, 7, [(2, 1), (5, 2), (7, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_89
  · decide +kernel

theorem prime_31153 : Nat.Prime 31153 := by
  apply nodeValid_prime [2, 3, 11, 59] ⟨31153, 10, [(2, 4), (3, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_31183 : Nat.Prime 31183 := by
  apply nodeValid_prime [2, 3, 5197] ⟨31183, 3, [(2, 1), (3, 1), (5197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5197
  · decide +kernel

theorem prime_31189 : Nat.Prime 31189 := by
  apply nodeValid_prime [2, 3, 23, 113] ⟨31189, 13, [(2, 2), (3, 1), (23, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_113
  · decide +kernel

theorem prime_31219 : Nat.Prime 31219 := by
  apply nodeValid_prime [2, 3, 11, 43] ⟨31219, 10, [(2, 1), (3, 1), (11, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_31237 : Nat.Prime 31237 := by
  apply nodeValid_prime [2, 3, 19, 137] ⟨31237, 6, [(2, 2), (3, 1), (19, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_31249 : Nat.Prime 31249 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨31249, 23, [(2, 4), (3, 2), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_31307 : Nat.Prime 31307 := by
  apply nodeValid_prime [2, 11, 1423] ⟨31307, 2, [(2, 1), (11, 1), (1423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1423
  · decide +kernel

theorem prime_31337 : Nat.Prime 31337 := by
  apply nodeValid_prime [2, 3917] ⟨31337, 3, [(2, 3), (3917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3917
  · decide +kernel

theorem prime_31357 : Nat.Prime 31357 := by
  apply nodeValid_prime [2, 3, 13, 67] ⟨31357, 2, [(2, 2), (3, 2), (13, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
  · decide +kernel

theorem prime_31379 : Nat.Prime 31379 := by
  apply nodeValid_prime [2, 29, 541] ⟨31379, 2, [(2, 1), (29, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_541
  · decide +kernel

theorem prime_31477 : Nat.Prime 31477 := by
  apply nodeValid_prime [2, 3, 43, 61] ⟨31477, 6, [(2, 2), (3, 1), (43, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_61
  · decide +kernel

theorem prime_31511 : Nat.Prime 31511 := by
  apply nodeValid_prime [2, 5, 23, 137] ⟨31511, 7, [(2, 1), (5, 1), (23, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_137
  · decide +kernel

theorem prime_31583 : Nat.Prime 31583 := by
  apply nodeValid_prime [2, 15791] ⟨31583, 5, [(2, 1), (15791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15791
  · decide +kernel

theorem prime_31601 : Nat.Prime 31601 := by
  apply nodeValid_prime [2, 5, 79] ⟨31601, 3, [(2, 4), (5, 2), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
  · decide +kernel

theorem prime_31607 : Nat.Prime 31607 := by
  apply nodeValid_prime [2, 15803] ⟨31607, 5, [(2, 1), (15803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_15803
  · decide +kernel

theorem prime_31643 : Nat.Prime 31643 := by
  apply nodeValid_prime [2, 13, 1217] ⟨31643, 2, [(2, 1), (13, 1), (1217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1217
  · decide +kernel

theorem prime_31663 : Nat.Prime 31663 := by
  apply nodeValid_prime [2, 3, 1759] ⟨31663, 3, [(2, 1), (3, 2), (1759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1759
  · decide +kernel

end Sude.Lucas.Generated
