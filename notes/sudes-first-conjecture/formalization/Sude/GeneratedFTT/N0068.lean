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
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0067

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2557 : Nat.Prime 2557 := by
  apply nodeValid_prime [2, 3, 71] ⟨2557, 2, [(2, 2), (3, 2), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel

theorem prime_5527 : Nat.Prime 5527 := by
  apply nodeValid_prime [2, 3, 307] ⟨5527, 5, [(2, 1), (3, 2), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_307
  · decide +kernel

theorem prime_5869 : Nat.Prime 5869 := by
  apply nodeValid_prime [2, 3, 163] ⟨5869, 2, [(2, 2), (3, 2), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
  · decide +kernel

theorem prime_6311 : Nat.Prime 6311 := by
  apply nodeValid_prime [2, 5, 631] ⟨6311, 7, [(2, 1), (5, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_631
  · decide +kernel

theorem prime_6551 : Nat.Prime 6551 := by
  apply nodeValid_prime [2, 5, 131] ⟨6551, 17, [(2, 1), (5, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
  · decide +kernel

theorem prime_8699 : Nat.Prime 8699 := by
  apply nodeValid_prime [2, 4349] ⟨8699, 2, [(2, 1), (4349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4349
  · decide +kernel

theorem prime_9887 : Nat.Prime 9887 := by
  apply nodeValid_prime [2, 4943] ⟨9887, 5, [(2, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4943
  · decide +kernel

theorem prime_12517 : Nat.Prime 12517 := by
  apply nodeValid_prime [2, 3, 7, 149] ⟨12517, 6, [(2, 2), (3, 1), (7, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_14753 : Nat.Prime 14753 := by
  apply nodeValid_prime [2, 461] ⟨14753, 3, [(2, 5), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_461
  · decide +kernel

theorem prime_15461 : Nat.Prime 15461 := by
  apply nodeValid_prime [2, 5, 773] ⟨15461, 2, [(2, 2), (5, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_773
  · decide +kernel

theorem prime_16831 : Nat.Prime 16831 := by
  apply nodeValid_prime [2, 3, 5, 11, 17] ⟨16831, 6, [(2, 1), (3, 2), (5, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_16901 : Nat.Prime 16901 := by
  apply nodeValid_prime [2, 5, 13] ⟨16901, 2, [(2, 2), (5, 2), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_22109 : Nat.Prime 22109 := by
  apply nodeValid_prime [2, 5527] ⟨22109, 2, [(2, 2), (5527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5527
  · decide +kernel

theorem prime_22777 : Nat.Prime 22777 := by
  apply nodeValid_prime [2, 3, 13, 73] ⟨22777, 7, [(2, 3), (3, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_26711 : Nat.Prime 26711 := by
  apply nodeValid_prime [2, 5, 2671] ⟨26711, 11, [(2, 1), (5, 1), (2671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2671
  · decide +kernel

theorem prime_29423 : Nat.Prime 29423 := by
  apply nodeValid_prime [2, 47, 313] ⟨29423, 5, [(2, 1), (47, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_313
  · decide +kernel

theorem prime_33857 : Nat.Prime 33857 := by
  apply nodeValid_prime [2, 23] ⟨33857, 3, [(2, 6), (23, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23
  · decide +kernel

theorem prime_34297 : Nat.Prime 34297 := by
  apply nodeValid_prime [2, 3, 1429] ⟨34297, 5, [(2, 3), (3, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1429
  · decide +kernel

theorem prime_39847 : Nat.Prime 39847 := by
  apply nodeValid_prime [2, 3, 29, 229] ⟨39847, 5, [(2, 1), (3, 1), (29, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_229
  · decide +kernel

theorem prime_40231 : Nat.Prime 40231 := by
  apply nodeValid_prime [2, 3, 5, 149] ⟨40231, 3, [(2, 1), (3, 3), (5, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
  · decide +kernel

theorem prime_42257 : Nat.Prime 42257 := by
  apply nodeValid_prime [2, 19, 139] ⟨42257, 3, [(2, 4), (19, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_139
  · decide +kernel

theorem prime_44971 : Nat.Prime 44971 := by
  apply nodeValid_prime [2, 3, 5, 1499] ⟨44971, 3, [(2, 1), (3, 1), (5, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1499
  · decide +kernel

theorem prime_45553 : Nat.Prime 45553 := by
  apply nodeValid_prime [2, 3, 13, 73] ⟨45553, 5, [(2, 4), (3, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_46829 : Nat.Prime 46829 := by
  apply nodeValid_prime [2, 23, 509] ⟨46829, 2, [(2, 2), (23, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_509
  · decide +kernel

theorem prime_56197 : Nat.Prime 56197 := by
  apply nodeValid_prime [2, 3, 7, 223] ⟨56197, 13, [(2, 2), (3, 2), (7, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_223
  · decide +kernel

theorem prime_57637 : Nat.Prime 57637 := by
  apply nodeValid_prime [2, 3, 1601] ⟨57637, 2, [(2, 2), (3, 2), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1601
  · decide +kernel

theorem prime_57973 : Nat.Prime 57973 := by
  apply nodeValid_prime [2, 3, 4831] ⟨57973, 5, [(2, 2), (3, 1), (4831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4831
  · decide +kernel

theorem prime_67891 : Nat.Prime 67891 := by
  apply nodeValid_prime [2, 3, 5, 31, 73] ⟨67891, 3, [(2, 1), (3, 1), (5, 1), (31, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_73
  · decide +kernel

theorem prime_74189 : Nat.Prime 74189 := by
  apply nodeValid_prime [2, 17, 1091] ⟨74189, 2, [(2, 2), (17, 1), (1091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1091
  · decide +kernel

theorem prime_92767 : Nat.Prime 92767 := by
  apply nodeValid_prime [2, 3, 15461] ⟨92767, 3, [(2, 1), (3, 1), (15461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15461
  · decide +kernel

theorem prime_96959 : Nat.Prime 96959 := by
  apply nodeValid_prime [2, 48479] ⟨96959, 7, [(2, 1), (48479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48479
  · decide +kernel

theorem prime_97021 : Nat.Prime 97021 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨97021, 2, [(2, 2), (3, 2), (5, 1), (7, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_106297 : Nat.Prime 106297 := by
  apply nodeValid_prime [2, 3, 43, 103] ⟨106297, 5, [(2, 3), (3, 1), (43, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_103
  · decide +kernel

theorem prime_107897 : Nat.Prime 107897 := by
  apply nodeValid_prime [2, 13487] ⟨107897, 3, [(2, 3), (13487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13487
  · decide +kernel

theorem prime_125687 : Nat.Prime 125687 := by
  apply nodeValid_prime [2, 11, 29, 197] ⟨125687, 5, [(2, 1), (11, 1), (29, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_197
  · decide +kernel

theorem prime_147139 : Nat.Prime 147139 := by
  apply nodeValid_prime [2, 3, 137, 179] ⟨147139, 2, [(2, 1), (3, 1), (137, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_179
  · decide +kernel

theorem prime_159389 : Nat.Prime 159389 := by
  apply nodeValid_prime [2, 39847] ⟨159389, 2, [(2, 2), (39847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39847
  · decide +kernel

theorem prime_160163 : Nat.Prime 160163 := by
  apply nodeValid_prime [2, 73, 1097] ⟨160163, 2, [(2, 1), (73, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1097
  · decide +kernel

theorem prime_162221 : Nat.Prime 162221 := by
  apply nodeValid_prime [2, 5, 8111] ⟨162221, 3, [(2, 2), (5, 1), (8111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8111
  · decide +kernel

theorem prime_162791 : Nat.Prime 162791 := by
  apply nodeValid_prime [2, 5, 73, 223] ⟨162791, 13, [(2, 1), (5, 1), (73, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_223
  · decide +kernel

theorem prime_163853 : Nat.Prime 163853 := by
  apply nodeValid_prime [2, 13, 23, 137] ⟨163853, 2, [(2, 2), (13, 1), (23, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_137
  · decide +kernel

theorem prime_167197 : Nat.Prime 167197 := by
  apply nodeValid_prime [2, 3, 13933] ⟨167197, 2, [(2, 2), (3, 1), (13933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13933
  · decide +kernel

theorem prime_170809 : Nat.Prime 170809 := by
  apply nodeValid_prime [2, 3, 11, 647] ⟨170809, 13, [(2, 3), (3, 1), (11, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_647
  · decide +kernel

theorem prime_224831 : Nat.Prime 224831 := by
  apply nodeValid_prime [2, 5, 22483] ⟨224831, 17, [(2, 1), (5, 1), (22483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22483
  · decide +kernel

theorem prime_231893 : Nat.Prime 231893 := by
  apply nodeValid_prime [2, 57973] ⟨231893, 2, [(2, 2), (57973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57973
  · decide +kernel

theorem prime_253543 : Nat.Prime 253543 := by
  apply nodeValid_prime [2, 3, 42257] ⟨253543, 3, [(2, 1), (3, 1), (42257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42257
  · decide +kernel

theorem prime_274457 : Nat.Prime 274457 := by
  apply nodeValid_prime [2, 7, 13, 29] ⟨274457, 3, [(2, 3), (7, 1), (13, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_312401 : Nat.Prime 312401 := by
  apply nodeValid_prime [2, 5, 11, 71] ⟨312401, 3, [(2, 4), (5, 2), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_327707 : Nat.Prime 327707 := by
  apply nodeValid_prime [2, 163853] ⟨327707, 2, [(2, 1), (163853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163853
  · decide +kernel

theorem prime_345701 : Nat.Prime 345701 := by
  apply nodeValid_prime [2, 5, 3457] ⟨345701, 2, [(2, 2), (5, 2), (3457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3457
  · decide +kernel

theorem prime_356023 : Nat.Prime 356023 := by
  apply nodeValid_prime [2, 3, 19, 347] ⟨356023, 13, [(2, 1), (3, 3), (19, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_347
  · decide +kernel

theorem prime_386161 : Nat.Prime 386161 := by
  apply nodeValid_prime [2, 3, 5, 1609] ⟨386161, 7, [(2, 4), (3, 1), (5, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1609
  · decide +kernel

theorem prime_463787 : Nat.Prime 463787 := by
  apply nodeValid_prime [2, 231893] ⟨463787, 2, [(2, 1), (231893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_231893
  · decide +kernel

theorem prime_472151 : Nat.Prime 472151 := by
  apply nodeValid_prime [2, 5, 7, 19, 71] ⟨472151, 7, [(2, 1), (5, 2), (7, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_508097 : Nat.Prime 508097 := by
  apply nodeValid_prime [2, 17, 467] ⟨508097, 3, [(2, 6), (17, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_467
  · decide +kernel

theorem prime_576749 : Nat.Prime 576749 := by
  apply nodeValid_prime [2, 23, 6269] ⟨576749, 2, [(2, 2), (23, 1), (6269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_6269
  · decide +kernel

theorem prime_624803 : Nat.Prime 624803 := by
  apply nodeValid_prime [2, 312401] ⟨624803, 2, [(2, 1), (312401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_312401
  · decide +kernel

theorem prime_624977 : Nat.Prime 624977 := by
  apply nodeValid_prime [2, 11, 53, 67] ⟨624977, 3, [(2, 4), (11, 1), (53, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_67
  · decide +kernel

theorem prime_673241 : Nat.Prime 673241 := by
  apply nodeValid_prime [2, 5, 16831] ⟨673241, 3, [(2, 3), (5, 1), (16831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16831
  · decide +kernel

theorem prime_727541 : Nat.Prime 727541 := by
  apply nodeValid_prime [2, 5, 11, 3307] ⟨727541, 2, [(2, 2), (5, 1), (11, 1), (3307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3307
  · decide +kernel

theorem prime_797033 : Nat.Prime 797033 := by
  apply nodeValid_prime [2, 67, 1487] ⟨797033, 3, [(2, 3), (67, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_1487
  · decide +kernel

theorem prime_921733 : Nat.Prime 921733 := by
  apply nodeValid_prime [2, 3, 7, 10973] ⟨921733, 5, [(2, 2), (3, 1), (7, 1), (10973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10973
  · decide +kernel

theorem prime_927671 : Nat.Prime 927671 := by
  apply nodeValid_prime [2, 5, 92767] ⟨927671, 23, [(2, 1), (5, 1), (92767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_92767
  · decide +kernel

theorem prime_1155899 : Nat.Prime 1155899 := by
  apply nodeValid_prime [2, 17, 33997] ⟨1155899, 2, [(2, 1), (17, 1), (33997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_33997
  · decide +kernel

theorem prime_1346483 : Nat.Prime 1346483 := by
  apply nodeValid_prime [2, 673241] ⟨1346483, 2, [(2, 1), (673241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_673241
  · decide +kernel

theorem prime_1503037 : Nat.Prime 1503037 := by
  apply nodeValid_prime [2, 3, 4639] ⟨1503037, 2, [(2, 2), (3, 4), (4639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4639
  · decide +kernel

theorem prime_1569817 : Nat.Prime 1569817 := by
  apply nodeValid_prime [2, 3, 21803] ⟨1569817, 5, [(2, 3), (3, 2), (21803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21803
  · decide +kernel

theorem prime_1746343 : Nat.Prime 1746343 := by
  apply nodeValid_prime [2, 3, 13, 17, 439] ⟨1746343, 3, [(2, 1), (3, 2), (13, 1), (17, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_439
  · decide +kernel

theorem prime_2316967 : Nat.Prime 2316967 := by
  apply nodeValid_prime [2, 3, 386161] ⟨2316967, 3, [(2, 1), (3, 1), (386161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_386161
  · decide +kernel

theorem prime_2863577 : Nat.Prime 2863577 := by
  apply nodeValid_prime [2, 29, 12343] ⟨2863577, 3, [(2, 3), (29, 1), (12343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_12343
  · decide +kernel

theorem prime_3044651 : Nat.Prime 3044651 := by
  apply nodeValid_prime [2, 5, 7, 8699] ⟨3044651, 2, [(2, 1), (5, 2), (7, 1), (8699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_8699
  · decide +kernel

theorem prime_3286739 : Nat.Prime 3286739 := by
  apply nodeValid_prime [2, 7, 13, 18059] ⟨3286739, 2, [(2, 1), (7, 1), (13, 1), (18059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_18059
  · decide +kernel

theorem prime_3365587 : Nat.Prime 3365587 := by
  apply nodeValid_prime [2, 3, 7, 26711] ⟨3365587, 7, [(2, 1), (3, 2), (7, 1), (26711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_26711
  · decide +kernel

theorem prime_3798367 : Nat.Prime 3798367 := by
  apply nodeValid_prime [2, 3, 11, 13, 19, 233] ⟨3798367, 5, [(2, 1), (3, 1), (11, 1), (13, 1), (19, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_233
  · decide +kernel

theorem prime_4396123 : Nat.Prime 4396123 := by
  apply nodeValid_prime [2, 3, 283, 863] ⟨4396123, 2, [(2, 1), (3, 2), (283, 1), (863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_863
  · decide +kernel

theorem prime_5124997 : Nat.Prime 5124997 := by
  apply nodeValid_prime [2, 3, 29, 4909] ⟨5124997, 2, [(2, 2), (3, 2), (29, 1), (4909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_4909
  · decide +kernel

theorem prime_5198057 : Nat.Prime 5198057 := by
  apply nodeValid_prime [2, 17, 37, 1033] ⟨5198057, 3, [(2, 3), (17, 1), (37, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_1033
  · decide +kernel

theorem prime_5281693 : Nat.Prime 5281693 := by
  apply nodeValid_prime [2, 3, 13, 33857] ⟨5281693, 5, [(2, 2), (3, 1), (13, 1), (33857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_33857
  · decide +kernel

theorem prime_5566027 : Nat.Prime 5566027 := by
  apply nodeValid_prime [2, 3, 927671] ⟨5566027, 2, [(2, 1), (3, 1), (927671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_927671
  · decide +kernel

theorem prime_6985373 : Nat.Prime 6985373 := by
  apply nodeValid_prime [2, 1746343] ⟨6985373, 2, [(2, 2), (1746343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1746343
  · decide +kernel

theorem prime_7642513 : Nat.Prime 7642513 := by
  apply nodeValid_prime [2, 3, 5897] ⟨7642513, 5, [(2, 4), (3, 4), (5897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5897
  · decide +kernel

theorem prime_8559563 : Nat.Prime 8559563 := by
  apply nodeValid_prime [2, 11, 229, 1699] ⟨8559563, 2, [(2, 1), (11, 1), (229, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_229
    · exact prime_1699
  · decide +kernel

theorem prime_8566163 : Nat.Prime 8566163 := by
  apply nodeValid_prime [2, 11, 401, 971] ⟨8566163, 2, [(2, 1), (11, 1), (401, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_401
    · exact prime_971
  · decide +kernel

theorem prime_9460669 : Nat.Prime 9460669 := by
  apply nodeValid_prime [2, 3, 7, 41, 67] ⟨9460669, 10, [(2, 2), (3, 1), (7, 1), (41, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_67
  · decide +kernel

theorem prime_14737769 : Nat.Prime 14737769 := by
  apply nodeValid_prime [2, 19, 96959] ⟨14737769, 3, [(2, 3), (19, 1), (96959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_96959
  · decide +kernel

theorem prime_15397253 : Nat.Prime 15397253 := by
  apply nodeValid_prime [2, 13, 22777] ⟨15397253, 2, [(2, 2), (13, 2), (22777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_22777
  · decide +kernel

theorem prime_17997571 : Nat.Prime 17997571 := by
  apply nodeValid_prime [2, 3, 5, 311, 643] ⟨17997571, 2, [(2, 1), (3, 2), (5, 1), (311, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_311
    · exact prime_643
  · decide +kernel

theorem prime_24275683 : Nat.Prime 24275683 := by
  apply nodeValid_prime [2, 3, 61, 22109] ⟨24275683, 2, [(2, 1), (3, 2), (61, 1), (22109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_22109
  · decide +kernel

theorem prime_24504607 : Nat.Prime 24504607 := by
  apply nodeValid_prime [2, 3, 7] ⟨24504607, 3, [(2, 1), (3, 6), (7, 5)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_28329061 : Nat.Prime 28329061 := by
  apply nodeValid_prime [2, 3, 5, 472151] ⟨28329061, 11, [(2, 2), (3, 1), (5, 1), (472151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_472151
  · decide +kernel

theorem prime_31248851 : Nat.Prime 31248851 := by
  apply nodeValid_prime [2, 5, 624977] ⟨31248851, 2, [(2, 1), (5, 2), (624977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_624977
  · decide +kernel

theorem prime_41912239 : Nat.Prime 41912239 := by
  apply nodeValid_prime [2, 3, 6985373] ⟨41912239, 3, [(2, 1), (3, 1), (6985373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6985373
  · decide +kernel

theorem prime_44595169 : Nat.Prime 44595169 := by
  apply nodeValid_prime [2, 3, 97, 4789] ⟨44595169, 7, [(2, 5), (3, 1), (97, 1), (4789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_4789
  · decide +kernel

theorem prime_46658551 : Nat.Prime 46658551 := by
  apply nodeValid_prime [2, 3, 5, 53, 5869] ⟨46658551, 6, [(2, 1), (3, 1), (5, 2), (53, 1), (5869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_5869
  · decide +kernel

theorem prime_47003059 : Nat.Prime 47003059 := by
  apply nodeValid_prime [2, 3, 59, 14753] ⟨47003059, 10, [(2, 1), (3, 3), (59, 1), (14753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_14753
  · decide +kernel

theorem prime_51556471 : Nat.Prime 51556471 := by
  apply nodeValid_prime [2, 3, 5, 7, 97, 2531] ⟨51556471, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (97, 1), (2531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_97
    · exact prime_2531
  · decide +kernel

theorem prime_100403029 : Nat.Prime 100403029 := by
  apply nodeValid_prime [2, 3, 11, 253543] ⟨100403029, 2, [(2, 2), (3, 2), (11, 1), (253543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_253543
  · decide +kernel

theorem prime_169614427 : Nat.Prime 169614427 := by
  apply nodeValid_prime [2, 3, 103, 274457] ⟨169614427, 3, [(2, 1), (3, 1), (103, 1), (274457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_274457
  · decide +kernel

theorem prime_215209703 : Nat.Prime 215209703 := by
  apply nodeValid_prime [2, 661, 162791] ⟨215209703, 5, [(2, 1), (661, 1), (162791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_661
    · exact prime_162791
  · decide +kernel

theorem prime_318919619 : Nat.Prime 318919619 := by
  apply nodeValid_prime [2, 173, 921733] ⟨318919619, 2, [(2, 1), (173, 1), (921733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_921733
  · decide +kernel

theorem prime_322079911 : Nat.Prime 322079911 := by
  apply nodeValid_prime [2, 3, 5, 101, 106297] ⟨322079911, 3, [(2, 1), (3, 1), (5, 1), (101, 1), (106297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_106297
  · decide +kernel

theorem prime_439482739 : Nat.Prime 439482739 := by
  apply nodeValid_prime [2, 3, 127, 576749] ⟨439482739, 2, [(2, 1), (3, 1), (127, 1), (576749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_576749
  · decide +kernel

theorem prime_486780787 : Nat.Prime 486780787 := by
  apply nodeValid_prime [2, 3, 23, 31, 47, 269] ⟨486780787, 2, [(2, 1), (3, 3), (23, 1), (31, 1), (47, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_31
    · exact prime_47
    · exact prime_269
  · decide +kernel

theorem prime_510876127 : Nat.Prime 510876127 := by
  apply nodeValid_prime [2, 3, 9460669] ⟨510876127, 3, [(2, 1), (3, 3), (9460669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9460669
  · decide +kernel

theorem prime_613286549 : Nat.Prime 613286549 := by
  apply nodeValid_prime [2, 7, 29, 107897] ⟨613286549, 2, [(2, 2), (7, 2), (29, 1), (107897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_107897
  · decide +kernel

theorem prime_637839239 : Nat.Prime 637839239 := by
  apply nodeValid_prime [2, 318919619] ⟨637839239, 7, [(2, 1), (318919619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_318919619
  · decide +kernel

theorem prime_768827827 : Nat.Prime 768827827 := by
  apply nodeValid_prime [2, 3, 13, 1373, 2393] ⟨768827827, 3, [(2, 1), (3, 2), (13, 1), (1373, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1373
    · exact prime_2393
  · decide +kernel

theorem prime_821718049 : Nat.Prime 821718049 := by
  apply nodeValid_prime [2, 3, 8559563] ⟨821718049, 7, [(2, 5), (3, 1), (8559563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8559563
  · decide +kernel

theorem prime_1226232949 : Nat.Prime 1226232949 := by
  apply nodeValid_prime [2, 3, 23, 151, 29423] ⟨1226232949, 10, [(2, 2), (3, 1), (23, 1), (151, 1), (29423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_151
    · exact prime_29423
  · decide +kernel

theorem prime_3005654581 : Nat.Prime 3005654581 := by
  apply nodeValid_prime [2, 3, 5, 5566027] ⟨3005654581, 2, [(2, 2), (3, 3), (5, 1), (5566027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5566027
  · decide +kernel

theorem prime_5521982023 : Nat.Prime 5521982023 := by
  apply nodeValid_prime [2, 3, 6551, 46829] ⟨5521982023, 3, [(2, 1), (3, 2), (6551, 1), (46829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6551
    · exact prime_46829
  · decide +kernel

theorem prime_7908656549 : Nat.Prime 7908656549 := by
  apply nodeValid_prime [2, 13, 11833, 12853] ⟨7908656549, 2, [(2, 2), (13, 1), (11833, 1), (12853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_11833
    · exact prime_12853
  · decide +kernel

theorem prime_14889485843 : Nat.Prime 14889485843 := by
  apply nodeValid_prime [2, 7, 11, 127, 9887] ⟨14889485843, 2, [(2, 1), (7, 2), (11, 2), (127, 1), (9887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_127
    · exact prime_9887
  · decide +kernel

theorem prime_20270644193 : Nat.Prime 20270644193 := by
  apply nodeValid_prime [2, 1933, 327707] ⟨20270644193, 3, [(2, 5), (1933, 1), (327707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1933
    · exact prime_327707
  · decide +kernel

theorem prime_21758212181 : Nat.Prime 21758212181 := by
  apply nodeValid_prime [2, 5, 331, 3286739] ⟨21758212181, 2, [(2, 2), (5, 1), (331, 1), (3286739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_331
    · exact prime_3286739
  · decide +kernel

theorem prime_21909971371 : Nat.Prime 21909971371 := by
  apply nodeValid_prime [2, 3, 5, 7, 31, 3365587] ⟨21909971371, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (3365587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_3365587
  · decide +kernel

theorem prime_34589565149 : Nat.Prime 34589565149 := by
  apply nodeValid_prime [2, 107, 643, 125687] ⟨34589565149, 2, [(2, 2), (107, 1), (643, 1), (125687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_643
    · exact prime_125687
  · decide +kernel

theorem prime_42728282767 : Nat.Prime 42728282767 := by
  apply nodeValid_prime [2, 3, 13, 17, 73, 147139] ⟨42728282767, 3, [(2, 1), (3, 2), (13, 1), (17, 1), (73, 1), (147139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_73
    · exact prime_147139
  · decide +kernel

theorem prime_237955178731 : Nat.Prime 237955178731 := by
  apply nodeValid_prime [2, 3, 5, 79, 100403029] ⟨237955178731, 3, [(2, 1), (3, 1), (5, 1), (79, 1), (100403029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_100403029
  · decide +kernel

theorem prime_242967208501 : Nat.Prime 242967208501 := by
  apply nodeValid_prime [2, 3, 5, 17997571] ⟨242967208501, 10, [(2, 2), (3, 3), (5, 3), (17997571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17997571
  · decide +kernel

theorem prime_360261042949 : Nat.Prime 360261042949 := by
  apply nodeValid_prime [2, 3, 59, 169614427] ⟨360261042949, 2, [(2, 2), (3, 2), (59, 1), (169614427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_169614427
  · decide +kernel

theorem prime_362770985569 : Nat.Prime 362770985569 := by
  apply nodeValid_prime [2, 3, 79, 1511, 31657] ⟨362770985569, 7, [(2, 5), (3, 1), (79, 1), (1511, 1), (31657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_1511
    · exact prime_31657
  · decide +kernel

theorem prime_716356864571 : Nat.Prime 716356864571 := by
  apply nodeValid_prime [2, 5, 163, 439482739] ⟨716356864571, 6, [(2, 1), (5, 1), (163, 1), (439482739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_439482739
  · decide +kernel

theorem prime_719687747231 : Nat.Prime 719687747231 := by
  apply nodeValid_prime [2, 5, 29, 157, 347, 45553] ⟨719687747231, 13, [(2, 1), (5, 1), (29, 1), (157, 1), (347, 1), (45553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_157
    · exact prime_347
    · exact prime_45553
  · decide +kernel

theorem prime_1419452759573 : Nat.Prime 1419452759573 := by
  apply nodeValid_prime [2, 6883, 51556471] ⟨1419452759573, 2, [(2, 2), (6883, 1), (51556471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6883
    · exact prime_51556471
  · decide +kernel

theorem prime_1419452761079 : Nat.Prime 1419452761079 := by
  apply nodeValid_prime [2, 11, 27847, 2316967] ⟨1419452761079, 11, [(2, 1), (11, 1), (27847, 1), (2316967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_27847
    · exact prime_2316967
  · decide +kernel

theorem prime_1419452774893 : Nat.Prime 1419452774893 := by
  apply nodeValid_prime [2, 3, 486780787] ⟨1419452774893, 2, [(2, 2), (3, 6), (486780787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_486780787
  · decide +kernel

theorem prime_1421105824493 : Nat.Prime 1421105824493 := by
  apply nodeValid_prime [2, 557, 637839239] ⟨1421105824493, 2, [(2, 2), (557, 1), (637839239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_557
    · exact prime_637839239
  · decide +kernel

theorem prime_1421105835301 : Nat.Prime 1421105835301 := by
  apply nodeValid_prime [2, 3, 5, 17, 383, 727541] ⟨1421105835301, 2, [(2, 2), (3, 1), (5, 2), (17, 1), (383, 1), (727541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_383
    · exact prime_727541
  · decide +kernel

theorem prime_1421105835913 : Nat.Prime 1421105835913 := by
  apply nodeValid_prime [2, 3, 7, 17, 131, 3798367] ⟨1421105835913, 10, [(2, 3), (3, 1), (7, 1), (17, 1), (131, 1), (3798367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_131
    · exact prime_3798367
  · decide +kernel

theorem prime_1422760181471 : Nat.Prime 1422760181471 := by
  apply nodeValid_prime [2, 5, 101, 271, 5198057] ⟨1422760181471, 13, [(2, 1), (5, 1), (101, 1), (271, 1), (5198057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_271
    · exact prime_5198057
  · decide +kernel

theorem prime_1422760185577 : Nat.Prime 1422760185577 := by
  apply nodeValid_prime [2, 3, 67891, 97021] ⟨1422760185577, 7, [(2, 3), (3, 3), (67891, 1), (97021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67891
    · exact prime_97021
  · decide +kernel

theorem prime_1422760186031 : Nat.Prime 1422760186031 := by
  apply nodeValid_prime [2, 5, 29, 157, 31248851] ⟨1422760186031, 7, [(2, 1), (5, 1), (29, 1), (157, 1), (31248851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_157
    · exact prime_31248851
  · decide +kernel

theorem prime_1424415848293 : Nat.Prime 1424415848293 := by
  apply nodeValid_prime [2, 3, 31, 149, 8566163] ⟨1424415848293, 2, [(2, 2), (3, 2), (31, 1), (149, 1), (8566163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_149
    · exact prime_8566163
  · decide +kernel

theorem prime_1424415881353 : Nat.Prime 1424415881353 := by
  apply nodeValid_prime [2, 3, 71, 5153, 162221] ⟨1424415881353, 5, [(2, 3), (3, 1), (71, 1), (5153, 1), (162221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_5153
    · exact prime_162221
  · decide +kernel

theorem prime_1424415882553 : Nat.Prime 1424415882553 := by
  apply nodeValid_prime [2, 3, 13, 7307, 624803] ⟨1424415882553, 10, [(2, 3), (3, 1), (13, 1), (7307, 1), (624803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_7307
    · exact prime_624803
  · decide +kernel

theorem prime_1426072800277 : Nat.Prime 1426072800277 := by
  apply nodeValid_prime [2, 3, 31, 101, 1607, 7873] ⟨1426072800277, 7, [(2, 2), (3, 2), (31, 1), (101, 1), (1607, 1), (7873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_101
    · exact prime_1607
    · exact prime_7873
  · decide +kernel

theorem prime_1426072801319 : Nat.Prime 1426072801319 := by
  apply nodeValid_prime [2, 11, 113, 1129, 508097] ⟨1426072801319, 11, [(2, 1), (11, 1), (113, 1), (1129, 1), (508097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113
    · exact prime_1129
    · exact prime_508097
  · decide +kernel

theorem prime_1426072810061 : Nat.Prime 1426072810061 := by
  apply nodeValid_prime [2, 5, 37, 41, 47003059] ⟨1426072810061, 3, [(2, 2), (5, 1), (37, 1), (41, 1), (47003059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_41
    · exact prime_47003059
  · decide +kernel

theorem prime_1427731072387 : Nat.Prime 1427731072387 := by
  apply nodeValid_prime [2, 3, 237955178731] ⟨1427731072387, 2, [(2, 1), (3, 1), (237955178731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_237955178731
  · decide +kernel

theorem prime_1427731085657 : Nat.Prime 1427731085657 := by
  apply nodeValid_prime [2, 193, 251, 839, 4391] ⟨1427731085657, 3, [(2, 3), (193, 1), (251, 1), (839, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_251
    · exact prime_839
    · exact prime_4391
  · decide +kernel

theorem prime_1427731086073 : Nat.Prime 1427731086073 := by
  apply nodeValid_prime [2, 3, 97, 613286549] ⟨1427731086073, 5, [(2, 3), (3, 1), (97, 1), (613286549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_613286549
  · decide +kernel

theorem prime_1429390640929 : Nat.Prime 1429390640929 := by
  apply nodeValid_prime [2, 3, 14889485843] ⟨1429390640929, 7, [(2, 5), (3, 1), (14889485843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14889485843
  · decide +kernel

theorem prime_1429390645019 : Nat.Prime 1429390645019 := by
  apply nodeValid_prime [2, 7, 317, 322079911] ⟨1429390645019, 2, [(2, 1), (7, 1), (317, 1), (322079911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_317
    · exact prime_322079911
  · decide +kernel

theorem prime_1431051488327 : Nat.Prime 1431051488327 := by
  apply nodeValid_prime [2, 46471, 15397253] ⟨1431051488327, 5, [(2, 1), (46471, 1), (15397253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_46471
    · exact prime_15397253
  · decide +kernel

theorem prime_1431051488417 : Nat.Prime 1431051488417 := by
  apply nodeValid_prime [2, 11, 97, 41912239] ⟨1431051488417, 3, [(2, 5), (11, 1), (97, 1), (41912239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_97
    · exact prime_41912239
  · decide +kernel

theorem prime_1431051512851 : Nat.Prime 1431051512851 := by
  apply nodeValid_prime [2, 3, 5, 131, 24275683] ⟨1431051512851, 3, [(2, 1), (3, 2), (5, 2), (131, 1), (24275683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_131
    · exact prime_24275683
  · decide +kernel

theorem prime_1432713692521 : Nat.Prime 1432713692521 := by
  apply nodeValid_prime [2, 3, 5, 11, 313, 1155899] ⟨1432713692521, 17, [(2, 3), (3, 2), (5, 1), (11, 1), (313, 1), (1155899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_313
    · exact prime_1155899
  · decide +kernel

theorem prime_1432713729143 : Nat.Prime 1432713729143 := by
  apply nodeValid_prime [2, 716356864571] ⟨1432713729143, 5, [(2, 1), (716356864571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_716356864571
  · decide +kernel

theorem prime_1432713729539 : Nat.Prime 1432713729539 := by
  apply nodeValid_prime [2, 7, 13, 311, 4409, 5741] ⟨1432713729539, 2, [(2, 1), (7, 1), (13, 1), (311, 1), (4409, 1), (5741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_311
    · exact prime_4409
    · exact prime_5741
  · decide +kernel

theorem prime_1434377173609 : Nat.Prime 1434377173609 := by
  apply nodeValid_prime [2, 3, 773, 2863577] ⟨1434377173609, 11, [(2, 3), (3, 4), (773, 1), (2863577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_773
    · exact prime_2863577
  · decide +kernel

theorem prime_1434377174843 : Nat.Prime 1434377174843 := by
  apply nodeValid_prime [2, 19, 809, 46658551] ⟨1434377174843, 2, [(2, 1), (19, 1), (809, 1), (46658551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_809
    · exact prime_46658551
  · decide +kernel

theorem prime_1434377181637 : Nat.Prime 1434377181637 := by
  apply nodeValid_prime [2, 3, 7, 71, 6311, 12703] ⟨1434377181637, 14, [(2, 2), (3, 2), (7, 1), (71, 1), (6311, 1), (12703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_6311
    · exact prime_12703
  · decide +kernel

theorem prime_1436041972853 : Nat.Prime 1436041972853 := by
  apply nodeValid_prime [2, 41, 137, 401, 159389] ⟨1436041972853, 2, [(2, 2), (41, 1), (137, 1), (401, 1), (159389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_137
    · exact prime_401
    · exact prime_159389
  · decide +kernel

theorem prime_1436042003947 : Nat.Prime 1436042003947 := by
  apply nodeValid_prime [2, 3, 11, 21758212181] ⟨1436042003947, 3, [(2, 1), (3, 1), (11, 1), (21758212181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_21758212181
  · decide +kernel

theorem prime_1436042004673 : Nat.Prime 1436042004673 := by
  apply nodeValid_prime [2, 3, 11, 16901, 40231] ⟨1436042004673, 5, [(2, 6), (3, 1), (11, 1), (16901, 1), (40231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_16901
    · exact prime_40231
  · decide +kernel

theorem prime_1437708036467 : Nat.Prime 1437708036467 := by
  apply nodeValid_prime [2, 13, 2971, 3083, 6037] ⟨1437708036467, 2, [(2, 1), (13, 1), (2971, 1), (3083, 1), (6037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2971
    · exact prime_3083
    · exact prime_6037
  · decide +kernel

theorem prime_1437708036491 : Nat.Prime 1437708036491 := by
  apply nodeValid_prime [2, 5, 11, 17, 768827827] ⟨1437708036491, 2, [(2, 1), (5, 1), (11, 1), (17, 1), (768827827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_768827827
  · decide +kernel

theorem prime_1437708065921 : Nat.Prime 1437708065921 := by
  apply nodeValid_prime [2, 5, 7, 73, 4396123] ⟨1437708065921, 15, [(2, 7), (5, 1), (7, 1), (73, 1), (4396123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_73
    · exact prime_4396123
  · decide +kernel

theorem prime_1439375464309 : Nat.Prime 1439375464309 := by
  apply nodeValid_prime [2, 3, 1013, 2633, 44971] ⟨1439375464309, 2, [(2, 2), (3, 1), (1013, 1), (2633, 1), (44971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1013
    · exact prime_2633
    · exact prime_44971
  · decide +kernel

theorem prime_1439375491919 : Nat.Prime 1439375491919 := by
  apply nodeValid_prime [2, 7, 13, 7908656549] ⟨1439375491919, 19, [(2, 1), (7, 1), (13, 1), (7908656549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_7908656549
  · decide +kernel

theorem prime_1439375494463 : Nat.Prime 1439375494463 := by
  apply nodeValid_prime [2, 719687747231] ⟨1439375494463, 5, [(2, 1), (719687747231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_719687747231
  · decide +kernel

theorem prime_1441044167569 : Nat.Prime 1441044167569 := by
  apply nodeValid_prime [2, 3, 19, 29, 31, 37, 67, 709] ⟨1441044167569, 7, [(2, 4), (3, 1), (19, 1), (29, 1), (31, 1), (37, 1), (67, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_31
    · exact prime_37
    · exact prime_67
    · exact prime_709
  · decide +kernel

theorem prime_1441044171289 : Nat.Prime 1441044171289 := by
  apply nodeValid_prime [2, 3, 31, 215209703] ⟨1441044171289, 11, [(2, 3), (3, 3), (31, 1), (215209703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_215209703
  · decide +kernel

theorem prime_1441044171797 : Nat.Prime 1441044171797 := by
  apply nodeValid_prime [2, 360261042949] ⟨1441044171797, 2, [(2, 2), (360261042949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_360261042949
  · decide +kernel

theorem prime_1442714182649 : Nat.Prime 1442714182649 := by
  apply nodeValid_prime [2, 353, 510876127] ⟨1442714182649, 3, [(2, 3), (353, 1), (510876127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_510876127
  · decide +kernel

theorem prime_1442714198719 : Nat.Prime 1442714198719 := by
  apply nodeValid_prime [2, 3, 13, 61, 181, 757, 2213] ⟨1442714198719, 3, [(2, 1), (3, 1), (13, 1), (61, 1), (181, 1), (757, 1), (2213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
    · exact prime_181
    · exact prime_757
    · exact prime_2213
  · decide +kernel

theorem prime_1442714198881 : Nat.Prime 1442714198881 := by
  apply nodeValid_prime [2, 3, 5, 3005654581] ⟨1442714198881, 11, [(2, 5), (3, 1), (5, 1), (3005654581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3005654581
  · decide +kernel

theorem prime_1444385490187 : Nat.Prime 1444385490187 := by
  apply nodeValid_prime [2, 3, 160163, 1503037] ⟨1444385490187, 3, [(2, 1), (3, 1), (160163, 1), (1503037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_160163
    · exact prime_1503037
  · decide +kernel

theorem prime_1444385492623 : Nat.Prime 1444385492623 := by
  apply nodeValid_prime [2, 3, 47, 2557, 74189] ⟨1444385492623, 3, [(2, 1), (3, 4), (47, 1), (2557, 1), (74189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_2557
    · exact prime_74189
  · decide +kernel

theorem prime_1444385504147 : Nat.Prime 1444385504147 := by
  apply nodeValid_prime [2, 13, 37, 53, 28329061] ⟨1444385504147, 2, [(2, 1), (13, 1), (37, 1), (53, 1), (28329061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_53
    · exact prime_28329061
  · decide +kernel

theorem prime_1446058110487 : Nat.Prime 1446058110487 := by
  apply nodeValid_prime [2, 3, 11, 21909971371] ⟨1446058110487, 7, [(2, 1), (3, 1), (11, 1), (21909971371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_21909971371
  · decide +kernel

theorem prime_1446058110817 : Nat.Prime 1446058110817 := by
  apply nodeValid_prime [2, 3, 11, 113, 1346483] ⟨1446058110817, 10, [(2, 5), (3, 3), (11, 1), (113, 1), (1346483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
    · exact prime_1346483
  · decide +kernel

theorem prime_1446058133237 : Nat.Prime 1446058133237 := by
  apply nodeValid_prime [2, 31, 51869, 224831] ⟨1446058133237, 2, [(2, 2), (31, 1), (51869, 1), (224831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_51869
    · exact prime_224831
  · decide +kernel

theorem prime_1447732071481 : Nat.Prime 1447732071481 := by
  apply nodeValid_prime [2, 3, 5, 59, 1223, 167197] ⟨1447732071481, 13, [(2, 3), (3, 1), (5, 1), (59, 1), (1223, 1), (167197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_1223
    · exact prime_167197
  · decide +kernel

theorem prime_1447732179017 : Nat.Prime 1447732179017 := by
  apply nodeValid_prime [2, 137, 3821, 345701] ⟨1447732179017, 3, [(2, 3), (137, 1), (3821, 1), (345701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_3821
    · exact prime_345701
  · decide +kernel

theorem prime_1447732181561 : Nat.Prime 1447732181561 := by
  apply nodeValid_prime [2, 5, 7, 211, 24504607] ⟨1447732181561, 6, [(2, 3), (5, 1), (7, 1), (211, 1), (24504607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_211
    · exact prime_24504607
  · decide +kernel

theorem prime_1449407312501 : Nat.Prime 1449407312501 := by
  apply nodeValid_prime [2, 5, 7, 29, 71, 1609] ⟨1449407312501, 2, [(2, 2), (5, 6), (7, 1), (29, 1), (71, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_71
    · exact prime_1609
  · decide +kernel

theorem prime_1449407345719 : Nat.Prime 1449407345719 := by
  apply nodeValid_prime [2, 3, 197, 1226232949] ⟨1449407345719, 3, [(2, 1), (3, 1), (197, 1), (1226232949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1226232949
  · decide +kernel

theorem prime_1449407346433 : Nat.Prime 1449407346433 := by
  apply nodeValid_prime [2, 3, 193, 271, 36083] ⟨1449407346433, 13, [(2, 8), (3, 1), (193, 1), (271, 1), (36083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_271
    · exact prime_36083
  · decide +kernel

theorem prime_1451083867073 : Nat.Prime 1451083867073 := by
  apply nodeValid_prime [2, 7, 56197, 57637] ⟨1451083867073, 3, [(2, 6), (7, 1), (56197, 1), (57637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_56197
    · exact prime_57637
  · decide +kernel

theorem prime_1451083942277 : Nat.Prime 1451083942277 := by
  apply nodeValid_prime [2, 362770985569] ⟨1451083942277, 2, [(2, 2), (362770985569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_362770985569
  · decide +kernel

theorem prime_1451083943311 : Nat.Prime 1451083943311 := by
  apply nodeValid_prime [2, 3, 5, 6329, 7642513] ⟨1451083943311, 3, [(2, 1), (3, 1), (5, 1), (6329, 1), (7642513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6329
    · exact prime_7642513
  · decide +kernel

theorem prime_1452761613497 : Nat.Prime 1452761613497 := by
  apply nodeValid_prime [2, 71, 3209, 797033] ⟨1452761613497, 3, [(2, 3), (71, 1), (3209, 1), (797033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_3209
    · exact prime_797033
  · decide +kernel

theorem prime_1452761614079 : Nat.Prime 1452761614079 := by
  apply nodeValid_prime [2, 17, 42728282767] ⟨1452761614079, 31, [(2, 1), (17, 1), (42728282767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_42728282767
  · decide +kernel

theorem prime_1452761736259 : Nat.Prime 1452761736259 := by
  apply nodeValid_prime [2, 3, 7, 34589565149] ⟨1452761736259, 7, [(2, 1), (3, 1), (7, 1), (34589565149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_34589565149
  · decide +kernel

theorem prime_1454440928183 : Nat.Prime 1454440928183 := by
  apply nodeValid_prime [2, 11, 12517, 5281693] ⟨1454440928183, 5, [(2, 1), (11, 1), (12517, 1), (5281693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_12517
    · exact prime_5281693
  · decide +kernel

theorem prime_1454440946731 : Nat.Prime 1454440946731 := by
  apply nodeValid_prime [2, 3, 5, 59, 821718049] ⟨1454440946731, 2, [(2, 1), (3, 1), (5, 1), (59, 1), (821718049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_821718049
  · decide +kernel

theorem prime_1454440947073 : Nat.Prime 1454440947073 := by
  apply nodeValid_prime [2, 3, 257, 14737769] ⟨1454440947073, 5, [(2, 7), (3, 1), (257, 1), (14737769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_14737769
  · decide +kernel

theorem prime_1456121433959 : Nat.Prime 1456121433959 := by
  apply nodeValid_prime [2, 463787, 1569817] ⟨1456121433959, 11, [(2, 1), (463787, 1), (1569817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_463787
    · exact prime_1569817
  · decide +kernel

theorem prime_1456121457499 : Nat.Prime 1456121457499 := by
  apply nodeValid_prime [2, 3, 443, 15973, 34297] ⟨1456121457499, 3, [(2, 1), (3, 1), (443, 1), (15973, 1), (34297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_443
    · exact prime_15973
    · exact prime_34297
  · decide +kernel

theorem prime_1456121458189 : Nat.Prime 1456121458189 := by
  apply nodeValid_prime [2, 3, 907, 44595169] ⟨1456121458189, 6, [(2, 2), (3, 2), (907, 1), (44595169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_907
    · exact prime_44595169
  · decide +kernel

theorem prime_1457803251007 : Nat.Prime 1457803251007 := by
  apply nodeValid_prime [2, 3, 242967208501] ⟨1457803251007, 3, [(2, 1), (3, 1), (242967208501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_242967208501
  · decide +kernel

theorem prime_1457803254073 : Nat.Prime 1457803254073 := by
  apply nodeValid_prime [2, 3, 11, 5521982023] ⟨1457803254073, 5, [(2, 3), (3, 1), (11, 1), (5521982023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5521982023
  · decide +kernel

theorem prime_1457803256009 : Nat.Prime 1457803256009 := by
  apply nodeValid_prime [2, 11, 5441, 3044651] ⟨1457803256009, 3, [(2, 3), (11, 1), (5441, 1), (3044651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_5441
    · exact prime_3044651
  · decide +kernel

theorem prime_1459486381897 : Nat.Prime 1459486381897 := by
  apply nodeValid_prime [2, 3, 20270644193] ⟨1459486381897, 13, [(2, 3), (3, 2), (20270644193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20270644193
  · decide +kernel

theorem prime_1459486382569 : Nat.Prime 1459486382569 := by
  apply nodeValid_prime [2, 3, 170809, 356023] ⟨1459486382569, 7, [(2, 3), (3, 1), (170809, 1), (356023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_170809
    · exact prime_356023
  · decide +kernel

theorem prime_1459486395667 : Nat.Prime 1459486395667 := by
  apply nodeValid_prime [2, 3, 13, 1217, 5124997] ⟨1459486395667, 3, [(2, 1), (3, 2), (13, 1), (1217, 1), (5124997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1217
    · exact prime_5124997
  · decide +kernel

end Sude.Lucas.Generated
