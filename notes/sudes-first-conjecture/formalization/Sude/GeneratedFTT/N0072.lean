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
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0059

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7933 : Nat.Prime 7933 := by
  apply nodeValid_prime [2, 3, 661] ⟨7933, 2, [(2, 2), (3, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_661
  · decide +kernel

theorem prime_10861 : Nat.Prime 10861 := by
  apply nodeValid_prime [2, 3, 5, 181] ⟨10861, 2, [(2, 2), (3, 1), (5, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
  · decide +kernel

theorem prime_11399 : Nat.Prime 11399 := by
  apply nodeValid_prime [2, 41, 139] ⟨11399, 11, [(2, 1), (41, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_139
  · decide +kernel

theorem prime_11813 : Nat.Prime 11813 := by
  apply nodeValid_prime [2, 2953] ⟨11813, 2, [(2, 2), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2953
  · decide +kernel

theorem prime_11831 : Nat.Prime 11831 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨11831, 7, [(2, 1), (5, 1), (7, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_12161 : Nat.Prime 12161 := by
  apply nodeValid_prime [2, 5, 19] ⟨12161, 3, [(2, 7), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_12527 : Nat.Prime 12527 := by
  apply nodeValid_prime [2, 6263] ⟨12527, 5, [(2, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6263
  · decide +kernel

theorem prime_12923 : Nat.Prime 12923 := by
  apply nodeValid_prime [2, 7, 13, 71] ⟨12923, 2, [(2, 1), (7, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_15401 : Nat.Prime 15401 := by
  apply nodeValid_prime [2, 5, 7, 11] ⟨15401, 6, [(2, 3), (5, 2), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_17419 : Nat.Prime 17419 := by
  apply nodeValid_prime [2, 3, 2903] ⟨17419, 3, [(2, 1), (3, 1), (2903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2903
  · decide +kernel

theorem prime_18269 : Nat.Prime 18269 := by
  apply nodeValid_prime [2, 4567] ⟨18269, 2, [(2, 2), (4567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4567
  · decide +kernel

theorem prime_19237 : Nat.Prime 19237 := by
  apply nodeValid_prime [2, 3, 7, 229] ⟨19237, 2, [(2, 2), (3, 1), (7, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_229
  · decide +kernel

theorem prime_22093 : Nat.Prime 22093 := by
  apply nodeValid_prime [2, 3, 7, 263] ⟨22093, 6, [(2, 2), (3, 1), (7, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_263
  · decide +kernel

theorem prime_22409 : Nat.Prime 22409 := by
  apply nodeValid_prime [2, 2801] ⟨22409, 3, [(2, 3), (2801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2801
  · decide +kernel

theorem prime_22697 : Nat.Prime 22697 := by
  apply nodeValid_prime [2, 2837] ⟨22697, 3, [(2, 3), (2837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2837
  · decide +kernel

theorem prime_27329 : Nat.Prime 27329 := by
  apply nodeValid_prime [2, 7, 61] ⟨27329, 3, [(2, 6), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_28901 : Nat.Prime 28901 := by
  apply nodeValid_prime [2, 5, 17] ⟨28901, 3, [(2, 2), (5, 2), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_28961 : Nat.Prime 28961 := by
  apply nodeValid_prime [2, 5, 181] ⟨28961, 3, [(2, 5), (5, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_181
  · decide +kernel

theorem prime_31543 : Nat.Prime 31543 := by
  apply nodeValid_prime [2, 3, 7, 751] ⟨31543, 3, [(2, 1), (3, 1), (7, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_751
  · decide +kernel

theorem prime_33613 : Nat.Prime 33613 := by
  apply nodeValid_prime [2, 3, 2801] ⟨33613, 5, [(2, 2), (3, 1), (2801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2801
  · decide +kernel

theorem prime_33751 : Nat.Prime 33751 := by
  apply nodeValid_prime [2, 3, 5] ⟨33751, 6, [(2, 1), (3, 3), (5, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_36131 : Nat.Prime 36131 := by
  apply nodeValid_prime [2, 5, 3613] ⟨36131, 2, [(2, 1), (5, 1), (3613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3613
  · decide +kernel

theorem prime_41957 : Nat.Prime 41957 := by
  apply nodeValid_prime [2, 17, 617] ⟨41957, 2, [(2, 2), (17, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_617
  · decide +kernel

theorem prime_47569 : Nat.Prime 47569 := by
  apply nodeValid_prime [2, 3, 991] ⟨47569, 17, [(2, 4), (3, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_991
  · decide +kernel

theorem prime_57803 : Nat.Prime 57803 := by
  apply nodeValid_prime [2, 28901] ⟨57803, 2, [(2, 1), (28901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28901
  · decide +kernel

theorem prime_87473 : Nat.Prime 87473 := by
  apply nodeValid_prime [2, 7, 11, 71] ⟨87473, 5, [(2, 4), (7, 1), (11, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_71
  · decide +kernel

theorem prime_87683 : Nat.Prime 87683 := by
  apply nodeValid_prime [2, 7, 6263] ⟨87683, 2, [(2, 1), (7, 1), (6263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6263
  · decide +kernel

theorem prime_92189 : Nat.Prime 92189 := by
  apply nodeValid_prime [2, 19, 1213] ⟨92189, 2, [(2, 2), (19, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1213
  · decide +kernel

theorem prime_105983 : Nat.Prime 105983 := by
  apply nodeValid_prime [2, 19, 2789] ⟨105983, 5, [(2, 1), (19, 1), (2789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2789
  · decide +kernel

theorem prime_123341 : Nat.Prime 123341 := by
  apply nodeValid_prime [2, 5, 7, 881] ⟨123341, 3, [(2, 2), (5, 1), (7, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_881
  · decide +kernel

theorem prime_130379 : Nat.Prime 130379 := by
  apply nodeValid_prime [2, 19, 47, 73] ⟨130379, 2, [(2, 1), (19, 1), (47, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_47
    · exact prime_73
  · decide +kernel

theorem prime_145361 : Nat.Prime 145361 := by
  apply nodeValid_prime [2, 5, 23, 79] ⟨145361, 6, [(2, 4), (5, 1), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_152111 : Nat.Prime 152111 := by
  apply nodeValid_prime [2, 5, 7, 41, 53] ⟨152111, 7, [(2, 1), (5, 1), (7, 1), (41, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_53
  · decide +kernel

theorem prime_160117 : Nat.Prime 160117 := by
  apply nodeValid_prime [2, 3, 11, 1213] ⟨160117, 2, [(2, 2), (3, 1), (11, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1213
  · decide +kernel

theorem prime_164249 : Nat.Prime 164249 := by
  apply nodeValid_prime [2, 7, 419] ⟨164249, 3, [(2, 3), (7, 2), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_419
  · decide +kernel

theorem prime_184913 : Nat.Prime 184913 := by
  apply nodeValid_prime [2, 7, 13, 127] ⟨184913, 3, [(2, 4), (7, 1), (13, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_127
  · decide +kernel

theorem prime_192677 : Nat.Prime 192677 := by
  apply nodeValid_prime [2, 11, 29, 151] ⟨192677, 2, [(2, 2), (11, 1), (29, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_151
  · decide +kernel

theorem prime_213727 : Nat.Prime 213727 := by
  apply nodeValid_prime [2, 3, 179, 199] ⟨213727, 6, [(2, 1), (3, 1), (179, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_199
  · decide +kernel

theorem prime_216401 : Nat.Prime 216401 := by
  apply nodeValid_prime [2, 5, 541] ⟨216401, 3, [(2, 4), (5, 2), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_541
  · decide +kernel

theorem prime_226783 : Nat.Prime 226783 := by
  apply nodeValid_prime [2, 3, 43, 293] ⟨226783, 3, [(2, 1), (3, 2), (43, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_293
  · decide +kernel

theorem prime_237967 : Nat.Prime 237967 := by
  apply nodeValid_prime [2, 3, 17, 2333] ⟨237967, 5, [(2, 1), (3, 1), (17, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2333
  · decide +kernel

theorem prime_289897 : Nat.Prime 289897 := by
  apply nodeValid_prime [2, 3, 47, 257] ⟨289897, 10, [(2, 3), (3, 1), (47, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_257
  · decide +kernel

theorem prime_299983 : Nat.Prime 299983 := by
  apply nodeValid_prime [2, 3, 17, 173] ⟨299983, 3, [(2, 1), (3, 1), (17, 2), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_173
  · decide +kernel

theorem prime_313727 : Nat.Prime 313727 := by
  apply nodeValid_prime [2, 7, 22409] ⟨313727, 7, [(2, 1), (7, 1), (22409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_22409
  · decide +kernel

theorem prime_352193 : Nat.Prime 352193 := by
  apply nodeValid_prime [2, 5503] ⟨352193, 3, [(2, 6), (5503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5503
  · decide +kernel

theorem prime_369827 : Nat.Prime 369827 := by
  apply nodeValid_prime [2, 184913] ⟨369827, 2, [(2, 1), (184913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_184913
  · decide +kernel

theorem prime_381443 : Nat.Prime 381443 := by
  apply nodeValid_prime [2, 269, 709] ⟨381443, 2, [(2, 1), (269, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_709
  · decide +kernel

theorem prime_434297 : Nat.Prime 434297 := by
  apply nodeValid_prime [2, 54287] ⟨434297, 3, [(2, 3), (54287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_54287
  · decide +kernel

theorem prime_499607 : Nat.Prime 499607 := by
  apply nodeValid_prime [2, 23, 10861] ⟨499607, 5, [(2, 1), (23, 1), (10861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_10861
  · decide +kernel

theorem prime_500389 : Nat.Prime 500389 := by
  apply nodeValid_prime [2, 3, 7, 23, 37] ⟨500389, 6, [(2, 2), (3, 1), (7, 2), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_760343 : Nat.Prime 760343 := by
  apply nodeValid_prime [2, 11, 17, 19, 107] ⟨760343, 5, [(2, 1), (11, 1), (17, 1), (19, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_107
  · decide +kernel

theorem prime_761261 : Nat.Prime 761261 := by
  apply nodeValid_prime [2, 5, 17, 2239] ⟨761261, 3, [(2, 2), (5, 1), (17, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2239
  · decide +kernel

theorem prime_791029 : Nat.Prime 791029 := by
  apply nodeValid_prime [2, 3, 7, 43, 73] ⟨791029, 6, [(2, 2), (3, 2), (7, 1), (43, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_43
    · exact prime_73
  · decide +kernel

theorem prime_965357 : Nat.Prime 965357 := by
  apply nodeValid_prime [2, 7, 23, 1499] ⟨965357, 3, [(2, 2), (7, 1), (23, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_1499
  · decide +kernel

theorem prime_1005637 : Nat.Prime 1005637 := by
  apply nodeValid_prime [2, 3, 181, 463] ⟨1005637, 2, [(2, 2), (3, 1), (181, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_463
  · decide +kernel

theorem prime_1111379 : Nat.Prime 1111379 := by
  apply nodeValid_prime [2, 43, 12923] ⟨1111379, 2, [(2, 1), (43, 1), (12923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_12923
  · decide +kernel

theorem prime_1703323 : Nat.Prime 1703323 := by
  apply nodeValid_prime [2, 3, 31543] ⟨1703323, 2, [(2, 1), (3, 3), (31543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31543
  · decide +kernel

theorem prime_2106341 : Nat.Prime 2106341 := by
  apply nodeValid_prime [2, 5, 19, 23, 241] ⟨2106341, 2, [(2, 2), (5, 1), (19, 1), (23, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_241
  · decide +kernel

theorem prime_2168347 : Nat.Prime 2168347 := by
  apply nodeValid_prime [2, 3, 283, 1277] ⟨2168347, 2, [(2, 1), (3, 1), (283, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1277
  · decide +kernel

theorem prime_2554049 : Nat.Prime 2554049 := by
  apply nodeValid_prime [2, 7, 5701] ⟨2554049, 3, [(2, 6), (7, 1), (5701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5701
  · decide +kernel

theorem prime_2726923 : Nat.Prime 2726923 := by
  apply nodeValid_prime [2, 3, 11, 79, 523] ⟨2726923, 3, [(2, 1), (3, 1), (11, 1), (79, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
    · exact prime_523
  · decide +kernel

theorem prime_2970287 : Nat.Prime 2970287 := by
  apply nodeValid_prime [2, 11, 37, 41, 89] ⟨2970287, 5, [(2, 1), (11, 1), (37, 1), (41, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_41
    · exact prime_89
  · decide +kernel

theorem prime_2999831 : Nat.Prime 2999831 := by
  apply nodeValid_prime [2, 5, 299983] ⟨2999831, 7, [(2, 1), (5, 1), (299983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_299983
  · decide +kernel

theorem prime_3053987 : Nat.Prime 3053987 := by
  apply nodeValid_prime [2, 13, 23, 5107] ⟨3053987, 2, [(2, 1), (13, 1), (23, 1), (5107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_5107
  · decide +kernel

theorem prime_4060801 : Nat.Prime 4060801 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨4060801, 7, [(2, 7), (3, 3), (5, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_6024587 : Nat.Prime 6024587 := by
  apply nodeValid_prime [2, 1103, 2731] ⟨6024587, 2, [(2, 1), (1103, 1), (2731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1103
    · exact prime_2731
  · decide +kernel

theorem prime_6260321 : Nat.Prime 6260321 := by
  apply nodeValid_prime [2, 5, 11, 3557] ⟨6260321, 3, [(2, 5), (5, 1), (11, 1), (3557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3557
  · decide +kernel

theorem prime_6588863 : Nat.Prime 6588863 := by
  apply nodeValid_prime [2, 7, 197, 2389] ⟨6588863, 7, [(2, 1), (7, 1), (197, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_197
    · exact prime_2389
  · decide +kernel

theorem prime_6813293 : Nat.Prime 6813293 := by
  apply nodeValid_prime [2, 1703323] ⟨6813293, 2, [(2, 2), (1703323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1703323
  · decide +kernel

theorem prime_7582277 : Nat.Prime 7582277 := by
  apply nodeValid_prime [2, 13, 43, 3391] ⟨7582277, 2, [(2, 2), (13, 1), (43, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_3391
  · decide +kernel

theorem prime_9397019 : Nat.Prime 9397019 := by
  apply nodeValid_prime [2, 23, 67, 3049] ⟨9397019, 2, [(2, 1), (23, 1), (67, 1), (3049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_67
    · exact prime_3049
  · decide +kernel

theorem prime_10354789 : Nat.Prime 10354789 := by
  apply nodeValid_prime [2, 3, 383, 751] ⟨10354789, 2, [(2, 2), (3, 2), (383, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_383
    · exact prime_751
  · decide +kernel

theorem prime_11360113 : Nat.Prime 11360113 := by
  apply nodeValid_prime [2, 3, 29, 8161] ⟨11360113, 5, [(2, 4), (3, 1), (29, 1), (8161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_8161
  · decide +kernel

theorem prime_12009337 : Nat.Prime 12009337 := by
  apply nodeValid_prime [2, 3, 500389] ⟨12009337, 5, [(2, 3), (3, 1), (500389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_500389
  · decide +kernel

theorem prime_12638047 : Nat.Prime 12638047 := by
  apply nodeValid_prime [2, 3, 2106341] ⟨12638047, 7, [(2, 1), (3, 1), (2106341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2106341
  · decide +kernel

theorem prime_13153289 : Nat.Prime 13153289 := by
  apply nodeValid_prime [2, 227, 7243] ⟨13153289, 3, [(2, 3), (227, 1), (7243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_7243
  · decide +kernel

theorem prime_13177727 : Nat.Prime 13177727 := by
  apply nodeValid_prime [2, 6588863] ⟨13177727, 5, [(2, 1), (6588863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6588863
  · decide +kernel

theorem prime_15654439 : Nat.Prime 15654439 := by
  apply nodeValid_prime [2, 3, 289897] ⟨15654439, 6, [(2, 1), (3, 3), (289897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_289897
  · decide +kernel

theorem prime_16941259 : Nat.Prime 16941259 := by
  apply nodeValid_prime [2, 3, 313727] ⟨16941259, 2, [(2, 1), (3, 3), (313727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313727
  · decide +kernel

theorem prime_18101467 : Nat.Prime 18101467 := by
  apply nodeValid_prime [2, 3, 1005637] ⟨18101467, 2, [(2, 1), (3, 2), (1005637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1005637
  · decide +kernel

theorem prime_20517823 : Nat.Prime 20517823 := by
  apply nodeValid_prime [2, 3, 13, 87683] ⟨20517823, 3, [(2, 1), (3, 2), (13, 1), (87683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_87683
  · decide +kernel

theorem prime_33992701 : Nat.Prime 33992701 := by
  apply nodeValid_prime [2, 3, 5, 7, 16187] ⟨33992701, 10, [(2, 2), (3, 1), (5, 2), (7, 1), (16187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_16187
  · decide +kernel

theorem prime_35675261 : Nat.Prime 35675261 := by
  apply nodeValid_prime [2, 5, 151, 11813] ⟨35675261, 2, [(2, 2), (5, 1), (151, 1), (11813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_11813
  · decide +kernel

theorem prime_42911357 : Nat.Prime 42911357 := by
  apply nodeValid_prime [2, 67, 160117] ⟨42911357, 2, [(2, 2), (67, 1), (160117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_160117
  · decide +kernel

theorem prime_60014467 : Nat.Prime 60014467 := by
  apply nodeValid_prime [2, 3, 1111379] ⟨60014467, 2, [(2, 1), (3, 3), (1111379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1111379
  · decide +kernel

theorem prime_67765037 : Nat.Prime 67765037 := by
  apply nodeValid_prime [2, 16941259] ⟨67765037, 2, [(2, 2), (16941259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16941259
  · decide +kernel

theorem prime_78295001 : Nat.Prime 78295001 := by
  apply nodeValid_prime [2, 5, 7, 2237] ⟨78295001, 12, [(2, 3), (5, 4), (7, 1), (2237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2237
  · decide +kernel

theorem prime_95386103 : Nat.Prime 95386103 := by
  apply nodeValid_prime [2, 7, 6813293] ⟨95386103, 5, [(2, 1), (7, 1), (6813293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6813293
  · decide +kernel

theorem prime_122539691 : Nat.Prime 122539691 := by
  apply nodeValid_prime [2, 5, 7, 13, 19237] ⟨122539691, 2, [(2, 1), (5, 1), (7, 2), (13, 1), (19237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19237
  · decide +kernel

theorem prime_126371431 : Nat.Prime 126371431 := by
  apply nodeValid_prime [2, 3, 5, 23, 41, 1489] ⟨126371431, 6, [(2, 1), (3, 2), (5, 1), (23, 1), (41, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_41
    · exact prime_1489
  · decide +kernel

theorem prime_134911391 : Nat.Prime 134911391 := by
  apply nodeValid_prime [2, 5, 2609, 5171] ⟨134911391, 29, [(2, 1), (5, 1), (2609, 1), (5171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2609
    · exact prime_5171
  · decide +kernel

theorem prime_190772207 : Nat.Prime 190772207 := by
  apply nodeValid_prime [2, 95386103] ⟨190772207, 5, [(2, 1), (95386103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_95386103
  · decide +kernel

theorem prime_197152673 : Nat.Prime 197152673 := by
  apply nodeValid_prime [2, 17, 29, 12497] ⟨197152673, 3, [(2, 5), (17, 1), (29, 1), (12497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_12497
  · decide +kernel

theorem prime_245079383 : Nat.Prime 245079383 := by
  apply nodeValid_prime [2, 122539691] ⟨245079383, 5, [(2, 1), (122539691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_122539691
  · decide +kernel

theorem prime_391138619 : Nat.Prime 391138619 := by
  apply nodeValid_prime [2, 13, 17, 37, 23917] ⟨391138619, 2, [(2, 1), (13, 1), (17, 1), (37, 1), (23917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_37
    · exact prime_23917
  · decide +kernel

theorem prime_432965249 : Nat.Prime 432965249 := by
  apply nodeValid_prime [2, 17, 23, 41, 211] ⟨432965249, 6, [(2, 7), (17, 1), (23, 1), (41, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_41
    · exact prime_211
  · decide +kernel

theorem prime_1154407087 : Nat.Prime 1154407087 := by
  apply nodeValid_prime [2, 3, 7, 3053987] ⟨1154407087, 3, [(2, 1), (3, 3), (7, 1), (3053987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3053987
  · decide +kernel

theorem prime_1182916039 : Nat.Prime 1182916039 := by
  apply nodeValid_prime [2, 3, 197152673] ⟨1182916039, 7, [(2, 1), (3, 1), (197152673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197152673
  · decide +kernel

theorem prime_1558207801 : Nat.Prime 1558207801 := by
  apply nodeValid_prime [2, 3, 5, 101, 2857] ⟨1558207801, 7, [(2, 3), (3, 3), (5, 2), (101, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_2857
  · decide +kernel

theorem prime_1783970057 : Nat.Prime 1783970057 := by
  apply nodeValid_prime [2, 11, 1667, 12161] ⟨1783970057, 3, [(2, 3), (11, 1), (1667, 1), (12161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1667
    · exact prime_12161
  · decide +kernel

theorem prime_2171181781 : Nat.Prime 2171181781 := by
  apply nodeValid_prime [2, 3, 5, 953, 4219] ⟨2171181781, 6, [(2, 2), (3, 3), (5, 1), (953, 1), (4219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_953
    · exact prime_4219
  · decide +kernel

theorem prime_3129108953 : Nat.Prime 3129108953 := by
  apply nodeValid_prime [2, 391138619] ⟨3129108953, 3, [(2, 3), (391138619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_391138619
  · decide +kernel

theorem prime_3463721993 : Nat.Prime 3463721993 := by
  apply nodeValid_prime [2, 432965249] ⟨3463721993, 3, [(2, 3), (432965249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_432965249
  · decide +kernel

theorem prime_3756430793 : Nat.Prime 3756430793 := by
  apply nodeValid_prime [2, 2437, 192677] ⟨3756430793, 3, [(2, 3), (2437, 1), (192677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2437
    · exact prime_192677
  · decide +kernel

theorem prime_3932125039 : Nat.Prime 3932125039 := by
  apply nodeValid_prime [2, 3, 503, 434297] ⟨3932125039, 3, [(2, 1), (3, 2), (503, 1), (434297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
    · exact prime_434297
  · decide +kernel

theorem prime_4490066683 : Nat.Prime 4490066683 := by
  apply nodeValid_prime [2, 3, 139, 199399] ⟨4490066683, 2, [(2, 1), (3, 4), (139, 1), (199399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_199399
  · decide +kernel

theorem prime_4659722489 : Nat.Prime 4659722489 := by
  apply nodeValid_prime [2, 19, 41, 263, 2843] ⟨4659722489, 3, [(2, 3), (19, 1), (41, 1), (263, 1), (2843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_263
    · exact prime_2843
  · decide +kernel

theorem prime_24010571891 : Nat.Prime 24010571891 := by
  apply nodeValid_prime [2, 5, 19, 126371431] ⟨24010571891, 10, [(2, 1), (5, 1), (19, 1), (126371431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_126371431
  · decide +kernel

theorem prime_27121248863 : Nat.Prime 27121248863 := by
  apply nodeValid_prime [2, 29, 37, 12638047] ⟨27121248863, 5, [(2, 1), (29, 1), (37, 1), (12638047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_37
    · exact prime_12638047
  · decide +kernel

theorem prime_34632212611 : Nat.Prime 34632212611 := by
  apply nodeValid_prime [2, 3, 5, 1154407087] ⟨34632212611, 2, [(2, 1), (3, 1), (5, 1), (1154407087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1154407087
  · decide +kernel

theorem prime_72331623541 : Nat.Prime 72331623541 := by
  apply nodeValid_prime [2, 3, 5, 11, 41, 43, 6907] ⟨72331623541, 6, [(2, 2), (3, 3), (5, 1), (11, 1), (41, 1), (43, 1), (6907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_41
    · exact prime_43
    · exact prime_6907
  · decide +kernel

theorem prime_135606242873 : Nat.Prime 135606242873 := by
  apply nodeValid_prime [2, 17, 11399, 87473] ⟨135606242873, 3, [(2, 3), (17, 1), (11399, 1), (87473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_11399
    · exact prime_87473
  · decide +kernel

theorem prime_269704856893 : Nat.Prime 269704856893 := by
  apply nodeValid_prime [2, 3, 19, 1182916039] ⟨269704856893, 5, [(2, 2), (3, 1), (19, 1), (1182916039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1182916039
  · decide +kernel

theorem prime_272119808293 : Nat.Prime 272119808293 := by
  apply nodeValid_prime [2, 3, 31, 67, 352193] ⟨272119808293, 5, [(2, 2), (3, 1), (31, 2), (67, 1), (352193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_67
    · exact prime_352193
  · decide +kernel

theorem prime_398270445037 : Nat.Prime 398270445037 := by
  apply nodeValid_prime [2, 3, 41957, 791029] ⟨398270445037, 2, [(2, 2), (3, 1), (41957, 1), (791029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41957
    · exact prime_791029
  · decide +kernel

theorem prime_402754220411 : Nat.Prime 402754220411 := by
  apply nodeValid_prime [2, 5, 17, 6211, 381443] ⟨402754220411, 2, [(2, 1), (5, 1), (17, 1), (6211, 1), (381443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_6211
    · exact prime_381443
  · decide +kernel

theorem prime_404557285303 : Nat.Prime 404557285303 := by
  apply nodeValid_prime [2, 3, 103, 12527, 17419] ⟨404557285303, 3, [(2, 1), (3, 2), (103, 1), (12527, 1), (17419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_12527
    · exact prime_17419
  · decide +kernel

theorem prime_805508440823 : Nat.Prime 805508440823 := by
  apply nodeValid_prime [2, 402754220411] ⟨805508440823, 5, [(2, 1), (402754220411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_402754220411
  · decide +kernel

theorem prime_1591295701361 : Nat.Prime 1591295701361 := by
  apply nodeValid_prime [2, 5, 1237, 2027, 7933] ⟨1591295701361, 6, [(2, 4), (5, 1), (1237, 1), (2027, 1), (7933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1237
    · exact prime_2027
    · exact prime_7933
  · decide +kernel

theorem prime_1591295716849 : Nat.Prime 1591295716849 := by
  apply nodeValid_prime [2, 3, 43, 8363, 92189] ⟨1591295716849, 7, [(2, 4), (3, 1), (43, 1), (8363, 1), (92189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_8363
    · exact prime_92189
  · decide +kernel

theorem prime_1591295717903 : Nat.Prime 1591295717903 := by
  apply nodeValid_prime [2, 11, 72331623541] ⟨1591295717903, 5, [(2, 1), (11, 1), (72331623541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_72331623541
  · decide +kernel

theorem prime_1593081759569 : Nat.Prime 1593081759569 := by
  apply nodeValid_prime [2, 13, 10061, 761261] ⟨1593081759569, 3, [(2, 4), (13, 1), (10061, 1), (761261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10061
    · exact prime_761261
  · decide +kernel

theorem prime_1593081780107 : Nat.Prime 1593081780107 := by
  apply nodeValid_prime [2, 23, 34632212611] ⟨1593081780107, 5, [(2, 1), (23, 1), (34632212611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_34632212611
  · decide +kernel

theorem prime_1593081780149 : Nat.Prime 1593081780149 := by
  apply nodeValid_prime [2, 398270445037] ⟨1593081780149, 2, [(2, 2), (398270445037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_398270445037
  · decide +kernel

theorem prime_1594869170371 : Nat.Prime 1594869170371 := by
  apply nodeValid_prime [2, 3, 5, 7, 97, 78295001] ⟨1594869170371, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (97, 1), (78295001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_97
    · exact prime_78295001
  · decide +kernel

theorem prime_1594869230953 : Nat.Prime 1594869230953 := by
  apply nodeValid_prime [2, 3, 14969, 18269] ⟨1594869230953, 5, [(2, 3), (3, 6), (14969, 1), (18269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14969
    · exact prime_18269
  · decide +kernel

theorem prime_1594869230959 : Nat.Prime 1594869230959 := by
  apply nodeValid_prime [2, 3, 149, 1783970057] ⟨1594869230959, 3, [(2, 1), (3, 1), (149, 1), (1783970057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_1783970057
  · decide +kernel

theorem prime_1596657934019 : Nat.Prime 1596657934019 := by
  apply nodeValid_prime [2, 7, 547, 3607, 57803] ⟨1596657934019, 2, [(2, 1), (7, 1), (547, 1), (3607, 1), (57803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_547
    · exact prime_3607
    · exact prime_57803
  · decide +kernel

theorem prime_1596657998203 : Nat.Prime 1596657998203 := by
  apply nodeValid_prime [2, 3, 61, 241, 18101467] ⟨1596657998203, 2, [(2, 1), (3, 1), (61, 1), (241, 1), (18101467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_241
    · exact prime_18101467
  · decide +kernel

theorem prime_1596658000879 : Nat.Prime 1596658000879 := by
  apply nodeValid_prime [2, 3, 130379, 226783] ⟨1596658000879, 3, [(2, 1), (3, 3), (130379, 1), (226783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130379
    · exact prime_226783
  · decide +kernel

theorem prime_1598448048251 : Nat.Prime 1598448048251 := by
  apply nodeValid_prime [2, 5, 149, 42911357] ⟨1598448048251, 2, [(2, 1), (5, 3), (149, 1), (42911357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_42911357
  · decide +kernel

theorem prime_1598448067903 : Nat.Prime 1598448067903 := by
  apply nodeValid_prime [2, 3, 7, 4271, 2970287] ⟨1598448067903, 3, [(2, 1), (3, 2), (7, 1), (4271, 1), (2970287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4271
    · exact prime_2970287
  · decide +kernel

theorem prime_1598448068353 : Nat.Prime 1598448068353 := by
  apply nodeValid_prime [2, 3, 67, 10354789] ⟨1598448068353, 5, [(2, 8), (3, 2), (67, 1), (10354789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_10354789
  · decide +kernel

theorem prime_1600239517819 : Nat.Prime 1600239517819 := by
  apply nodeValid_prime [2, 3, 71, 3756430793] ⟨1600239517819, 2, [(2, 1), (3, 1), (71, 1), (3756430793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_3756430793
  · decide +kernel

theorem prime_1600239560767 : Nat.Prime 1600239560767 := by
  apply nodeValid_prime [2, 3, 7, 11, 3463721993] ⟨1600239560767, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (3463721993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_3463721993
  · decide +kernel

theorem prime_1600239560851 : Nat.Prime 1600239560851 := by
  apply nodeValid_prime [2, 3, 5, 7, 67, 7582277] ⟨1600239560851, 10, [(2, 1), (3, 2), (5, 2), (7, 1), (67, 1), (7582277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_67
    · exact prime_7582277
  · decide +kernel

theorem prime_1602032268659 : Nat.Prime 1602032268659 := by
  apply nodeValid_prime [2, 17, 257, 3301, 55541] ⟨1602032268659, 6, [(2, 1), (17, 1), (257, 1), (3301, 1), (55541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_257
    · exact prime_3301
    · exact prime_55541
  · decide +kernel

theorem prime_1602032269927 : Nat.Prime 1602032269927 := by
  apply nodeValid_prime [2, 3, 11, 977, 4091, 6073] ⟨1602032269927, 3, [(2, 1), (3, 1), (11, 1), (977, 1), (4091, 1), (6073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_977
    · exact prime_4091
    · exact prime_6073
  · decide +kernel

theorem prime_1602032343349 : Nat.Prime 1602032343349 := by
  apply nodeValid_prime [2, 3, 167, 313, 2554049] ⟨1602032343349, 2, [(2, 2), (3, 1), (167, 1), (313, 1), (2554049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_313
    · exact prime_2554049
  · decide +kernel

theorem prime_1603826531939 : Nat.Prime 1603826531939 := by
  apply nodeValid_prime [2, 369827, 2168347] ⟨1603826531939, 2, [(2, 1), (369827, 1), (2168347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_369827
    · exact prime_2168347
  · decide +kernel

theorem prime_1603826616109 : Nat.Prime 1603826616109 := by
  apply nodeValid_prime [2, 3, 17, 131, 60014467] ⟨1603826616109, 6, [(2, 2), (3, 1), (17, 1), (131, 1), (60014467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_131
    · exact prime_60014467
  · decide +kernel

theorem prime_1603826616209 : Nat.Prime 1603826616209 := by
  apply nodeValid_prime [2, 743, 134911391] ⟨1603826616209, 3, [(2, 4), (743, 1), (134911391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_743
    · exact prime_134911391
  · decide +kernel

theorem prime_1605621988231 : Nat.Prime 1605621988231 := by
  apply nodeValid_prime [2, 3, 5, 13, 313, 13153289] ⟨1605621988231, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (313, 1), (13153289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_313
    · exact prime_13153289
  · decide +kernel

theorem prime_1605621988391 : Nat.Prime 1605621988391 := by
  apply nodeValid_prime [2, 5, 7, 31, 1481, 499607] ⟨1605621988391, 11, [(2, 1), (5, 1), (7, 1), (31, 1), (1481, 1), (499607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_1481
    · exact prime_499607
  · decide +kernel

theorem prime_1605622088797 : Nat.Prime 1605622088797 := by
  apply nodeValid_prime [2, 3, 11, 29, 67, 6260321] ⟨1605622088797, 2, [(2, 2), (3, 1), (11, 1), (29, 1), (67, 1), (6260321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_67
    · exact prime_6260321
  · decide +kernel

theorem prime_1607419015667 : Nat.Prime 1607419015667 := by
  apply nodeValid_prime [2, 71, 47569, 237967] ⟨1607419015667, 2, [(2, 1), (71, 1), (47569, 1), (237967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_47569
    · exact prime_237967
  · decide +kernel

theorem prime_1607419139369 : Nat.Prime 1607419139369 := by
  apply nodeValid_prime [2, 7, 113, 179, 28961] ⟨1607419139369, 3, [(2, 3), (7, 3), (113, 1), (179, 1), (28961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_179
    · exact prime_28961
  · decide +kernel

theorem prime_1607419139461 : Nat.Prime 1607419139461 := by
  apply nodeValid_prime [2, 3, 5, 19, 107, 13177727] ⟨1607419139461, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (107, 1), (13177727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_107
    · exact prime_13177727
  · decide +kernel

theorem prime_1609217254531 : Nat.Prime 1609217254531 := by
  apply nodeValid_prime [2, 3, 5, 41, 47, 61, 152111] ⟨1609217254531, 2, [(2, 1), (3, 2), (5, 1), (41, 1), (47, 1), (61, 1), (152111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_47
    · exact prime_61
    · exact prime_152111
  · decide +kernel

theorem prime_1609217254607 : Nat.Prime 1609217254607 := by
  apply nodeValid_prime [2, 13, 22697, 2726923] ⟨1609217254607, 5, [(2, 1), (13, 1), (22697, 1), (2726923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_22697
    · exact prime_2726923
  · decide +kernel

theorem prime_1609217297549 : Nat.Prime 1609217297549 := by
  apply nodeValid_prime [2, 7, 131, 577, 760343] ⟨1609217297549, 2, [(2, 2), (7, 1), (131, 1), (577, 1), (760343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_577
    · exact prime_760343
  · decide +kernel

theorem prime_1611016881503 : Nat.Prime 1611016881503 := by
  apply nodeValid_prime [2, 7, 53, 2171181781] ⟨1611016881503, 7, [(2, 1), (7, 1), (53, 1), (2171181781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_2171181781
  · decide +kernel

theorem prime_1611016881647 : Nat.Prime 1611016881647 := by
  apply nodeValid_prime [2, 805508440823] ⟨1611016881647, 5, [(2, 1), (805508440823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_805508440823
  · decide +kernel

theorem prime_1611016935119 : Nat.Prime 1611016935119 := by
  apply nodeValid_prime [2, 929, 5279, 164249] ⟨1611016935119, 7, [(2, 1), (929, 1), (5279, 1), (164249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_929
    · exact prime_5279
    · exact prime_164249
  · decide +kernel

theorem prime_1612817935727 : Nat.Prime 1612817935727 := by
  apply nodeValid_prime [2, 17, 307, 10343, 14939] ⟨1612817935727, 5, [(2, 1), (17, 1), (307, 1), (10343, 1), (14939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_307
    · exact prime_10343
    · exact prime_14939
  · decide +kernel

theorem prime_1612817962837 : Nat.Prime 1612817962837 := by
  apply nodeValid_prime [2, 3, 11831, 11360113] ⟨1612817962837, 2, [(2, 2), (3, 1), (11831, 1), (11360113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11831
    · exact prime_11360113
  · decide +kernel

theorem prime_1612817963431 : Nat.Prime 1612817963431 := by
  apply nodeValid_prime [2, 3, 5, 19, 541, 811, 6449] ⟨1612817963431, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (541, 1), (811, 1), (6449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_541
    · exact prime_811
    · exact prime_6449
  · decide +kernel

theorem prime_1614620219567 : Nat.Prime 1614620219567 := by
  apply nodeValid_prime [2, 1973, 2293, 178447] ⟨1614620219567, 5, [(2, 1), (1973, 1), (2293, 1), (178447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1973
    · exact prime_2293
    · exact prime_178447
  · decide +kernel

theorem prime_1614620219749 : Nat.Prime 1614620219749 := by
  apply nodeValid_prime [2, 3, 43, 3129108953] ⟨1614620219749, 2, [(2, 2), (3, 1), (43, 1), (3129108953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_3129108953
  · decide +kernel

theorem prime_1614620296829 : Nat.Prime 1614620296829 := by
  apply nodeValid_prime [2, 7, 11, 599, 1229, 7121] ⟨1614620296829, 3, [(2, 2), (7, 1), (11, 1), (599, 1), (1229, 1), (7121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_599
    · exact prime_1229
    · exact prime_7121
  · decide +kernel

theorem prime_1616424005477 : Nat.Prime 1616424005477 := by
  apply nodeValid_prime [2, 7, 17, 281, 547, 22093] ⟨1616424005477, 2, [(2, 2), (7, 1), (17, 1), (281, 1), (547, 1), (22093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_281
    · exact prime_547
    · exact prime_22093
  · decide +kernel

theorem prime_1616424005881 : Nat.Prime 1616424005881 := by
  apply nodeValid_prime [2, 3, 5, 4490066683] ⟨1616424005881, 7, [(2, 3), (3, 2), (5, 1), (4490066683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4490066683
  · decide +kernel

theorem prime_1616424014167 : Nat.Prime 1616424014167 := by
  apply nodeValid_prime [2, 3, 13, 19, 37, 239, 123341] ⟨1616424014167, 38, [(2, 1), (3, 1), (13, 1), (19, 1), (37, 1), (239, 1), (123341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_37
    · exact prime_239
    · exact prime_123341
  · decide +kernel

theorem prime_1618229083561 : Nat.Prime 1618229083561 := by
  apply nodeValid_prime [2, 3, 5, 199, 67765037] ⟨1618229083561, 17, [(2, 3), (3, 1), (5, 1), (199, 1), (67765037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_67765037
  · decide +kernel

theorem prime_1618229141213 : Nat.Prime 1618229141213 := by
  apply nodeValid_prime [2, 404557285303] ⟨1618229141213, 2, [(2, 2), (404557285303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_404557285303
  · decide +kernel

theorem prime_1618229141359 : Nat.Prime 1618229141359 := by
  apply nodeValid_prime [2, 3, 269704856893] ⟨1618229141359, 3, [(2, 1), (3, 1), (269704856893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269704856893
  · decide +kernel

theorem prime_1620035516069 : Nat.Prime 1620035516069 := by
  apply nodeValid_prime [2, 103, 3932125039] ⟨1620035516069, 2, [(2, 2), (103, 1), (3932125039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_3932125039
  · decide +kernel

theorem prime_1620035542627 : Nat.Prime 1620035542627 := by
  apply nodeValid_prime [2, 3, 22483, 12009337] ⟨1620035542627, 2, [(2, 1), (3, 1), (22483, 1), (12009337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22483
    · exact prime_12009337
  · decide +kernel

theorem prime_1620035542649 : Nat.Prime 1620035542649 := by
  apply nodeValid_prime [2, 33613, 6024587] ⟨1620035542649, 3, [(2, 3), (33613, 1), (6024587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_33613
    · exact prime_6024587
  · decide +kernel

theorem prime_1621843262621 : Nat.Prime 1621843262621 := by
  apply nodeValid_prime [2, 5, 7, 17, 47, 67, 216401] ⟨1621843262621, 3, [(2, 2), (5, 1), (7, 1), (17, 1), (47, 1), (67, 1), (216401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_47
    · exact prime_67
    · exact prime_216401
  · decide +kernel

theorem prime_1621843262629 : Nat.Prime 1621843262629 := by
  apply nodeValid_prime [2, 3, 53, 331, 145361] ⟨1621843262629, 6, [(2, 2), (3, 1), (53, 2), (331, 1), (145361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_331
    · exact prime_145361
  · decide +kernel

theorem prime_1621843311391 : Nat.Prime 1621843311391 := by
  apply nodeValid_prime [2, 3, 5, 13313, 4060801] ⟨1621843311391, 6, [(2, 1), (3, 1), (5, 1), (13313, 1), (4060801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13313
    · exact prime_4060801
  · decide +kernel

theorem prime_1623652478633 : Nat.Prime 1623652478633 := by
  apply nodeValid_prime [2, 5689, 35675261] ⟨1623652478633, 3, [(2, 3), (5689, 1), (35675261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5689
    · exact prime_35675261
  · decide +kernel

theorem prime_1623652528643 : Nat.Prime 1623652528643 := by
  apply nodeValid_prime [2, 521, 1558207801] ⟨1623652528643, 2, [(2, 1), (521, 1), (1558207801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_521
    · exact prime_1558207801
  · decide +kernel

theorem prime_1623652529089 : Nat.Prime 1623652529089 := by
  apply nodeValid_prime [2, 3, 2819, 2999831] ⟨1623652529089, 7, [(2, 6), (3, 1), (2819, 1), (2999831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2819
    · exact prime_2999831
  · decide +kernel

theorem prime_1625462973707 : Nat.Prime 1625462973707 := by
  apply nodeValid_prime [2, 11, 13, 277, 20517823] ⟨1625462973707, 2, [(2, 1), (11, 1), (13, 1), (277, 1), (20517823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_277
    · exact prime_20517823
  · decide +kernel

theorem prime_1625462976419 : Nat.Prime 1625462976419 := by
  apply nodeValid_prime [2, 23909, 33992701] ⟨1625462976419, 2, [(2, 1), (23909, 1), (33992701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23909
    · exact prime_33992701
  · decide +kernel

theorem prime_1625463019127 : Nat.Prime 1625463019127 := by
  apply nodeValid_prime [2, 193, 269, 15654439] ⟨1625463019127, 5, [(2, 1), (193, 1), (269, 1), (15654439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_269
    · exact prime_15654439
  · decide +kernel

theorem prime_1627274914477 : Nat.Prime 1627274914477 := by
  apply nodeValid_prime [2, 3, 135606242873] ⟨1627274914477, 5, [(2, 2), (3, 1), (135606242873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_135606242873
  · decide +kernel

theorem prime_1627274915153 : Nat.Prime 1627274915153 := by
  apply nodeValid_prime [2, 103, 27329, 36131] ⟨1627274915153, 3, [(2, 4), (103, 1), (27329, 1), (36131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_27329
    · exact prime_36131
  · decide +kernel

theorem prime_1627274931781 : Nat.Prime 1627274931781 := by
  apply nodeValid_prime [2, 3, 5, 27121248863] ⟨1627274931781, 6, [(2, 2), (3, 1), (5, 1), (27121248863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27121248863
  · decide +kernel

theorem prime_1629088205351 : Nat.Prime 1629088205351 := by
  apply nodeValid_prime [2, 5, 33751, 965357] ⟨1629088205351, 23, [(2, 1), (5, 2), (33751, 1), (965357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33751
    · exact prime_965357
  · decide +kernel

theorem prime_1629088205449 : Nat.Prime 1629088205449 := by
  apply nodeValid_prime [2, 3, 11, 23, 139, 227, 773] ⟨1629088205449, 7, [(2, 3), (3, 1), (11, 2), (23, 1), (139, 1), (227, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_139
    · exact prime_227
    · exact prime_773
  · decide +kernel

theorem prime_1629088210081 : Nat.Prime 1629088210081 := by
  apply nodeValid_prime [2, 3, 5, 17, 29, 149, 15401] ⟨1629088210081, 13, [(2, 5), (3, 2), (5, 1), (17, 1), (29, 1), (149, 1), (15401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_29
    · exact prime_149
    · exact prime_15401
  · decide +kernel

theorem prime_1630902862153 : Nat.Prime 1630902862153 := by
  apply nodeValid_prime [2, 3, 105983, 213727] ⟨1630902862153, 10, [(2, 3), (3, 2), (105983, 1), (213727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105983
    · exact prime_213727
  · decide +kernel

theorem prime_1630902871151 : Nat.Prime 1630902871151 := by
  apply nodeValid_prime [2, 5, 7, 4659722489] ⟨1630902871151, 11, [(2, 1), (5, 2), (7, 1), (4659722489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_4659722489
  · decide +kernel

theorem prime_1630902872161 : Nat.Prime 1630902872161 := by
  apply nodeValid_prime [2, 3, 5, 3307, 38053] ⟨1630902872161, 7, [(2, 5), (3, 4), (5, 1), (3307, 1), (38053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3307
    · exact prime_38053
  · decide +kernel

theorem prime_1632718849547 : Nat.Prime 1632718849547 := by
  apply nodeValid_prime [2, 3331, 245079383] ⟨1632718849547, 2, [(2, 1), (3331, 1), (245079383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3331
    · exact prime_245079383
  · decide +kernel

theorem prime_1632718849759 : Nat.Prime 1632718849759 := by
  apply nodeValid_prime [2, 3, 272119808293] ⟨1632718849759, 3, [(2, 1), (3, 1), (272119808293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_272119808293
  · decide +kernel

theorem prime_1632718888589 : Nat.Prime 1632718888589 := by
  apply nodeValid_prime [2, 17, 24010571891] ⟨1632718888589, 2, [(2, 2), (17, 1), (24010571891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_24010571891
  · decide +kernel

theorem prime_1634536269577 : Nat.Prime 1634536269577 := by
  apply nodeValid_prime [2, 3, 7, 17, 190772207] ⟨1634536269577, 11, [(2, 3), (3, 2), (7, 1), (17, 1), (190772207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_190772207
  · decide +kernel

theorem prime_1634536278899 : Nat.Prime 1634536278899 := by
  apply nodeValid_prime [2, 29, 2999, 9397019] ⟨1634536278899, 2, [(2, 1), (29, 1), (2999, 1), (9397019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_2999
    · exact prime_9397019
  · decide +kernel

end Sude.Lucas.Generated
