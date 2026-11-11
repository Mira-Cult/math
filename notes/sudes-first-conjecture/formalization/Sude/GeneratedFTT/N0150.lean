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
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0134

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10067 : Nat.Prime 10067 := by
  apply nodeValid_prime [2, 7, 719] ⟨10067, 2, [(2, 1), (7, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_719
  · decide +kernel

theorem prime_12511 : Nat.Prime 12511 := by
  apply nodeValid_prime [2, 3, 5, 139] ⟨12511, 3, [(2, 1), (3, 2), (5, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
  · decide +kernel

theorem prime_14437 : Nat.Prime 14437 := by
  apply nodeValid_prime [2, 3, 401] ⟨14437, 5, [(2, 2), (3, 2), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
  · decide +kernel

theorem prime_15377 : Nat.Prime 15377 := by
  apply nodeValid_prime [2, 31] ⟨15377, 3, [(2, 4), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_31
  · decide +kernel

theorem prime_17483 : Nat.Prime 17483 := by
  apply nodeValid_prime [2, 8741] ⟨17483, 2, [(2, 1), (8741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8741
  · decide +kernel

theorem prime_26759 : Nat.Prime 26759 := by
  apply nodeValid_prime [2, 17, 787] ⟨26759, 13, [(2, 1), (17, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_787
  · decide +kernel

theorem prime_26981 : Nat.Prime 26981 := by
  apply nodeValid_prime [2, 5, 19, 71] ⟨26981, 3, [(2, 2), (5, 1), (19, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_71
  · decide +kernel

theorem prime_31873 : Nat.Prime 31873 := by
  apply nodeValid_prime [2, 3, 83] ⟨31873, 11, [(2, 7), (3, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_33353 : Nat.Prime 33353 := by
  apply nodeValid_prime [2, 11, 379] ⟨33353, 3, [(2, 3), (11, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_379
  · decide +kernel

theorem prime_35251 : Nat.Prime 35251 := by
  apply nodeValid_prime [2, 3, 5, 47] ⟨35251, 3, [(2, 1), (3, 1), (5, 3), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
  · decide +kernel

theorem prime_39367 : Nat.Prime 39367 := by
  apply nodeValid_prime [2, 3] ⟨39367, 3, [(2, 1), (3, 9)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_42923 : Nat.Prime 42923 := by
  apply nodeValid_prime [2, 11, 1951] ⟨42923, 2, [(2, 1), (11, 1), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1951
  · decide +kernel

theorem prime_43481 : Nat.Prime 43481 := by
  apply nodeValid_prime [2, 5, 1087] ⟨43481, 6, [(2, 3), (5, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1087
  · decide +kernel

theorem prime_44621 : Nat.Prime 44621 := by
  apply nodeValid_prime [2, 5, 23, 97] ⟨44621, 2, [(2, 2), (5, 1), (23, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_97
  · decide +kernel

theorem prime_47459 : Nat.Prime 47459 := by
  apply nodeValid_prime [2, 61, 389] ⟨47459, 2, [(2, 1), (61, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_389
  · decide +kernel

theorem prime_50909 : Nat.Prime 50909 := by
  apply nodeValid_prime [2, 11, 13, 89] ⟨50909, 2, [(2, 2), (11, 1), (13, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_89
  · decide +kernel

theorem prime_56911 : Nat.Prime 56911 := by
  apply nodeValid_prime [2, 3, 5, 7, 271] ⟨56911, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_271
  · decide +kernel

theorem prime_58787 : Nat.Prime 58787 := by
  apply nodeValid_prime [2, 7, 13, 17, 19] ⟨58787, 2, [(2, 1), (7, 1), (13, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_64217 : Nat.Prime 64217 := by
  apply nodeValid_prime [2, 23, 349] ⟨64217, 3, [(2, 3), (23, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_349
  · decide +kernel

theorem prime_72859 : Nat.Prime 72859 := by
  apply nodeValid_prime [2, 3, 12143] ⟨72859, 2, [(2, 1), (3, 1), (12143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12143
  · decide +kernel

theorem prime_78367 : Nat.Prime 78367 := by
  apply nodeValid_prime [2, 3, 37, 353] ⟨78367, 5, [(2, 1), (3, 1), (37, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_353
  · decide +kernel

theorem prime_80473 : Nat.Prime 80473 := by
  apply nodeValid_prime [2, 3, 7, 479] ⟨80473, 5, [(2, 3), (3, 1), (7, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_479
  · decide +kernel

theorem prime_80537 : Nat.Prime 80537 := by
  apply nodeValid_prime [2, 10067] ⟨80537, 3, [(2, 3), (10067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10067
  · decide +kernel

theorem prime_94889 : Nat.Prime 94889 := by
  apply nodeValid_prime [2, 29, 409] ⟨94889, 3, [(2, 3), (29, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_409
  · decide +kernel

theorem prime_107717 : Nat.Prime 107717 := by
  apply nodeValid_prime [2, 7, 3847] ⟨107717, 2, [(2, 2), (7, 1), (3847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3847
  · decide +kernel

theorem prime_114319 : Nat.Prime 114319 := by
  apply nodeValid_prime [2, 3, 29, 73] ⟨114319, 6, [(2, 1), (3, 3), (29, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_73
  · decide +kernel

theorem prime_149323 : Nat.Prime 149323 := by
  apply nodeValid_prime [2, 3, 41, 607] ⟨149323, 2, [(2, 1), (3, 1), (41, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_607
  · decide +kernel

theorem prime_178261 : Nat.Prime 178261 := by
  apply nodeValid_prime [2, 3, 5, 2971] ⟨178261, 6, [(2, 2), (3, 1), (5, 1), (2971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2971
  · decide +kernel

theorem prime_193031 : Nat.Prime 193031 := by
  apply nodeValid_prime [2, 5, 97, 199] ⟨193031, 11, [(2, 1), (5, 1), (97, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_199
  · decide +kernel

theorem prime_215279 : Nat.Prime 215279 := by
  apply nodeValid_prime [2, 7, 15377] ⟨215279, 7, [(2, 1), (7, 1), (15377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15377
  · decide +kernel

theorem prime_230393 : Nat.Prime 230393 := by
  apply nodeValid_prime [2, 31, 929] ⟨230393, 3, [(2, 3), (31, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_929
  · decide +kernel

theorem prime_257539 : Nat.Prime 257539 := by
  apply nodeValid_prime [2, 3, 42923] ⟨257539, 2, [(2, 1), (3, 1), (42923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42923
  · decide +kernel

theorem prime_264059 : Nat.Prime 264059 := by
  apply nodeValid_prime [2, 31, 4259] ⟨264059, 2, [(2, 1), (31, 1), (4259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_4259
  · decide +kernel

theorem prime_270689 : Nat.Prime 270689 := by
  apply nodeValid_prime [2, 11, 769] ⟨270689, 3, [(2, 5), (11, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_769
  · decide +kernel

theorem prime_321109 : Nat.Prime 321109 := by
  apply nodeValid_prime [2, 3, 26759] ⟨321109, 2, [(2, 2), (3, 1), (26759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26759
  · decide +kernel

theorem prime_358769 : Nat.Prime 358769 := by
  apply nodeValid_prime [2, 17, 1319] ⟨358769, 6, [(2, 4), (17, 1), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1319
  · decide +kernel

theorem prime_368243 : Nat.Prime 368243 := by
  apply nodeValid_prime [2, 7, 29, 907] ⟨368243, 2, [(2, 1), (7, 1), (29, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_907
  · decide +kernel

theorem prime_380929 : Nat.Prime 380929 := by
  apply nodeValid_prime [2, 3, 31] ⟨380929, 7, [(2, 12), (3, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_393697 : Nat.Prime 393697 := by
  apply nodeValid_prime [2, 3, 1367] ⟨393697, 5, [(2, 5), (3, 2), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1367
  · decide +kernel

theorem prime_433393 : Nat.Prime 433393 := by
  apply nodeValid_prime [2, 3, 9029] ⟨433393, 5, [(2, 4), (3, 1), (9029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9029
  · decide +kernel

theorem prime_502597 : Nat.Prime 502597 := by
  apply nodeValid_prime [2, 3, 23, 607] ⟨502597, 2, [(2, 2), (3, 2), (23, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_607
  · decide +kernel

theorem prime_564017 : Nat.Prime 564017 := by
  apply nodeValid_prime [2, 35251] ⟨564017, 3, [(2, 4), (35251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_35251
  · decide +kernel

theorem prime_696481 : Nat.Prime 696481 := by
  apply nodeValid_prime [2, 3, 5, 1451] ⟨696481, 13, [(2, 5), (3, 1), (5, 1), (1451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1451
  · decide +kernel

theorem prime_717539 : Nat.Prime 717539 := by
  apply nodeValid_prime [2, 358769] ⟨717539, 2, [(2, 1), (358769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_358769
  · decide +kernel

theorem prime_751631 : Nat.Prime 751631 := by
  apply nodeValid_prime [2, 5, 11, 6833] ⟨751631, 17, [(2, 1), (5, 1), (11, 1), (6833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_6833
  · decide +kernel

theorem prime_788651 : Nat.Prime 788651 := by
  apply nodeValid_prime [2, 5, 15773] ⟨788651, 10, [(2, 1), (5, 2), (15773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15773
  · decide +kernel

theorem prime_854263 : Nat.Prime 854263 := by
  apply nodeValid_prime [2, 3, 47459] ⟨854263, 3, [(2, 1), (3, 2), (47459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47459
  · decide +kernel

theorem prime_880091 : Nat.Prime 880091 := by
  apply nodeValid_prime [2, 5, 17, 31, 167] ⟨880091, 2, [(2, 1), (5, 1), (17, 1), (31, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_167
  · decide +kernel

theorem prime_945949 : Nat.Prime 945949 := by
  apply nodeValid_prime [2, 3, 17, 4637] ⟨945949, 6, [(2, 2), (3, 1), (17, 1), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_4637
  · decide +kernel

theorem prime_950819 : Nat.Prime 950819 := by
  apply nodeValid_prime [2, 11, 3929] ⟨950819, 6, [(2, 1), (11, 2), (3929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3929
  · decide +kernel

theorem prime_1143071 : Nat.Prime 1143071 := by
  apply nodeValid_prime [2, 5, 151, 757] ⟨1143071, 13, [(2, 1), (5, 1), (151, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_757
  · decide +kernel

theorem prime_1245091 : Nat.Prime 1245091 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨1245091, 10, [(2, 1), (3, 1), (5, 1), (7, 3), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_1365239 : Nat.Prime 1365239 := by
  apply nodeValid_prime [2, 7, 13931] ⟨1365239, 7, [(2, 1), (7, 2), (13931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13931
  · decide +kernel

theorem prime_1419097 : Nat.Prime 1419097 := by
  apply nodeValid_prime [2, 3, 7, 8447] ⟨1419097, 15, [(2, 3), (3, 1), (7, 1), (8447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8447
  · decide +kernel

theorem prime_1435079 : Nat.Prime 1435079 := by
  apply nodeValid_prime [2, 717539] ⟨1435079, 7, [(2, 1), (717539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_717539
  · decide +kernel

theorem prime_1503263 : Nat.Prime 1503263 := by
  apply nodeValid_prime [2, 751631] ⟨1503263, 5, [(2, 1), (751631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_751631
  · decide +kernel

theorem prime_1509307 : Nat.Prime 1509307 := by
  apply nodeValid_prime [2, 3, 23, 10937] ⟨1509307, 3, [(2, 1), (3, 1), (23, 1), (10937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_10937
  · decide +kernel

theorem prime_1782611 : Nat.Prime 1782611 := by
  apply nodeValid_prime [2, 5, 178261] ⟨1782611, 2, [(2, 1), (5, 1), (178261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_178261
  · decide +kernel

theorem prime_2040053 : Nat.Prime 2040053 := by
  apply nodeValid_prime [2, 7, 72859] ⟨2040053, 2, [(2, 2), (7, 1), (72859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_72859
  · decide +kernel

theorem prime_3090469 : Nat.Prime 3090469 := by
  apply nodeValid_prime [2, 3, 257539] ⟨3090469, 2, [(2, 2), (3, 1), (257539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257539
  · decide +kernel

theorem prime_3421637 : Nat.Prime 3421637 := by
  apply nodeValid_prime [2, 149, 5741] ⟨3421637, 2, [(2, 2), (149, 1), (5741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_5741
  · decide +kernel

theorem prime_3536219 : Nat.Prime 3536219 := by
  apply nodeValid_prime [2, 7, 229, 1103] ⟨3536219, 6, [(2, 1), (7, 1), (229, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_229
    · exact prime_1103
  · decide +kernel

theorem prime_3783797 : Nat.Prime 3783797 := by
  apply nodeValid_prime [2, 945949] ⟨3783797, 2, [(2, 2), (945949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_945949
  · decide +kernel

theorem prime_3886847 : Nat.Prime 3886847 := by
  apply nodeValid_prime [2, 17, 114319] ⟨3886847, 5, [(2, 1), (17, 1), (114319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_114319
  · decide +kernel

theorem prime_4019879 : Nat.Prime 4019879 := by
  apply nodeValid_prime [2, 71, 28309] ⟨4019879, 13, [(2, 1), (71, 1), (28309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_28309
  · decide +kernel

theorem prime_4041929 : Nat.Prime 4041929 := by
  apply nodeValid_prime [2, 11, 23, 1997] ⟨4041929, 6, [(2, 3), (11, 1), (23, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_1997
  · decide +kernel

theorem prime_5025971 : Nat.Prime 5025971 := by
  apply nodeValid_prime [2, 5, 502597] ⟨5025971, 10, [(2, 1), (5, 1), (502597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_502597
  · decide +kernel

theorem prime_5345281 : Nat.Prime 5345281 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨5345281, 13, [(2, 12), (3, 2), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_5354311 : Nat.Prime 5354311 := by
  apply nodeValid_prime [2, 3, 5, 13, 13729] ⟨5354311, 12, [(2, 1), (3, 1), (5, 1), (13, 1), (13729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_13729
  · decide +kernel

theorem prime_6246941 : Nat.Prime 6246941 := by
  apply nodeValid_prime [2, 5, 7, 44621] ⟨6246941, 2, [(2, 2), (5, 1), (7, 1), (44621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_44621
  · decide +kernel

theorem prime_7251733 : Nat.Prime 7251733 := by
  apply nodeValid_prime [2, 3, 201437] ⟨7251733, 2, [(2, 2), (3, 2), (201437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_201437
  · decide +kernel

theorem prime_7706617 : Nat.Prime 7706617 := by
  apply nodeValid_prime [2, 3, 321109] ⟨7706617, 10, [(2, 3), (3, 1), (321109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_321109
  · decide +kernel

theorem prime_7925699 : Nat.Prime 7925699 := by
  apply nodeValid_prime [2, 11, 19, 67, 283] ⟨7925699, 2, [(2, 1), (11, 1), (19, 1), (67, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_67
    · exact prime_283
  · decide +kernel

theorem prime_9019579 : Nat.Prime 9019579 := by
  apply nodeValid_prime [2, 3, 1503263] ⟨9019579, 3, [(2, 1), (3, 1), (1503263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1503263
  · decide +kernel

theorem prime_10017853 : Nat.Prime 10017853 := by
  apply nodeValid_prime [2, 3, 13, 64217] ⟨10017853, 5, [(2, 2), (3, 1), (13, 1), (64217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_64217
  · decide +kernel

theorem prime_11613733 : Nat.Prime 11613733 := by
  apply nodeValid_prime [2, 3, 13, 109, 683] ⟨11613733, 2, [(2, 2), (3, 1), (13, 1), (109, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_109
    · exact prime_683
  · decide +kernel

theorem prime_14260889 : Nat.Prime 14260889 := by
  apply nodeValid_prime [2, 1782611] ⟨14260889, 3, [(2, 3), (1782611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1782611
  · decide +kernel

theorem prime_24113813 : Nat.Prime 24113813 := by
  apply nodeValid_prime [2, 19, 97, 3271] ⟨24113813, 2, [(2, 2), (19, 1), (97, 1), (3271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_97
    · exact prime_3271
  · decide +kernel

theorem prime_25236833 : Nat.Prime 25236833 := by
  apply nodeValid_prime [2, 788651] ⟨25236833, 3, [(2, 5), (788651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_788651
  · decide +kernel

theorem prime_37691317 : Nat.Prime 37691317 := by
  apply nodeValid_prime [2, 3, 13, 80537] ⟨37691317, 2, [(2, 2), (3, 2), (13, 1), (80537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_80537
  · decide +kernel

theorem prime_40071413 : Nat.Prime 40071413 := by
  apply nodeValid_prime [2, 10017853] ⟨40071413, 2, [(2, 2), (10017853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10017853
  · decide +kernel

theorem prime_47264137 : Nat.Prime 47264137 := by
  apply nodeValid_prime [2, 3, 467, 4217] ⟨47264137, 10, [(2, 3), (3, 1), (467, 1), (4217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_467
    · exact prime_4217
  · decide +kernel

theorem prime_56692369 : Nat.Prime 56692369 := by
  apply nodeValid_prime [2, 3, 393697] ⟨56692369, 7, [(2, 4), (3, 2), (393697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_393697
  · decide +kernel

theorem prime_72296839 : Nat.Prime 72296839 := by
  apply nodeValid_prime [2, 3, 271, 14821] ⟨72296839, 6, [(2, 1), (3, 2), (271, 1), (14821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
    · exact prime_14821
  · decide +kernel

theorem prime_74025221 : Nat.Prime 74025221 := by
  apply nodeValid_prime [2, 5, 787, 4703] ⟨74025221, 2, [(2, 2), (5, 1), (787, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_787
    · exact prime_4703
  · decide +kernel

theorem prime_88412173 : Nat.Prime 88412173 := by
  apply nodeValid_prime [2, 3, 17, 433393] ⟨88412173, 5, [(2, 2), (3, 1), (17, 1), (433393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_433393
  · decide +kernel

theorem prime_120046103 : Nat.Prime 120046103 := by
  apply nodeValid_prime [2, 11, 853, 6397] ⟨120046103, 5, [(2, 1), (11, 1), (853, 1), (6397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_853
    · exact prime_6397
  · decide +kernel

theorem prime_131925697 : Nat.Prime 131925697 := by
  apply nodeValid_prime [2, 3, 7, 103, 953] ⟨131925697, 10, [(2, 6), (3, 1), (7, 1), (103, 1), (953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_953
  · decide +kernel

theorem prime_170443223 : Nat.Prime 170443223 := by
  apply nodeValid_prime [2, 5903, 14437] ⟨170443223, 5, [(2, 1), (5903, 1), (14437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5903
    · exact prime_14437
  · decide +kernel

theorem prime_214650473 : Nat.Prime 214650473 := by
  apply nodeValid_prime [2, 139, 193031] ⟨214650473, 3, [(2, 3), (139, 1), (193031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_193031
  · decide +kernel

theorem prime_251637469 : Nat.Prime 251637469 := by
  apply nodeValid_prime [2, 3, 17, 653, 1889] ⟨251637469, 6, [(2, 2), (3, 1), (17, 1), (653, 1), (1889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_653
    · exact prime_1889
  · decide +kernel

theorem prime_330087701 : Nat.Prime 330087701 := by
  apply nodeValid_prime [2, 5, 1223, 2699] ⟨330087701, 2, [(2, 2), (5, 2), (1223, 1), (2699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1223
    · exact prime_2699
  · decide +kernel

theorem prime_351803723 : Nat.Prime 351803723 := by
  apply nodeValid_prime [2, 23, 71, 107717] ⟨351803723, 2, [(2, 1), (23, 1), (71, 1), (107717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_71
    · exact prime_107717
  · decide +kernel

theorem prime_352656637 : Nat.Prime 352656637 := by
  apply nodeValid_prime [2, 3, 17, 271, 6379] ⟨352656637, 2, [(2, 2), (3, 1), (17, 1), (271, 1), (6379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_271
    · exact prime_6379
  · decide +kernel

theorem prime_360694339 : Nat.Prime 360694339 := by
  apply nodeValid_prime [2, 3, 17, 3536219] ⟨360694339, 2, [(2, 1), (3, 1), (17, 1), (3536219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3536219
  · decide +kernel

theorem prime_429300947 : Nat.Prime 429300947 := by
  apply nodeValid_prime [2, 214650473] ⟨429300947, 2, [(2, 1), (214650473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_214650473
  · decide +kernel

theorem prime_483503101 : Nat.Prime 483503101 := by
  apply nodeValid_prime [2, 3, 5, 47, 53, 647] ⟨483503101, 2, [(2, 2), (3, 1), (5, 2), (47, 1), (53, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_53
    · exact prime_647
  · decide +kernel

theorem prime_491393339 : Nat.Prime 491393339 := by
  apply nodeValid_prime [2, 31, 7925699] ⟨491393339, 2, [(2, 1), (31, 1), (7925699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_7925699
  · decide +kernel

theorem prime_684522673 : Nat.Prime 684522673 := by
  apply nodeValid_prime [2, 3, 14260889] ⟨684522673, 10, [(2, 4), (3, 1), (14260889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14260889
  · decide +kernel

theorem prime_1012428289 : Nat.Prime 1012428289 := by
  apply nodeValid_prime [2, 3, 73237] ⟨1012428289, 14, [(2, 9), (3, 3), (73237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73237
  · decide +kernel

theorem prime_1202142391 : Nat.Prime 1202142391 := by
  apply nodeValid_prime [2, 3, 5, 40071413] ⟨1202142391, 7, [(2, 1), (3, 1), (5, 1), (40071413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_40071413
  · decide +kernel

theorem prime_1277953379 : Nat.Prime 1277953379 := by
  apply nodeValid_prime [2, 13, 43, 1143071] ⟨1277953379, 2, [(2, 1), (13, 1), (43, 1), (1143071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_1143071
  · decide +kernel

theorem prime_1386252853 : Nat.Prime 1386252853 := by
  apply nodeValid_prime [2, 3, 157, 839, 877] ⟨1386252853, 2, [(2, 2), (3, 1), (157, 1), (839, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_839
    · exact prime_877
  · decide +kernel

theorem prime_2126409349 : Nat.Prime 2126409349 := by
  apply nodeValid_prime [2, 3, 7, 1609, 15733] ⟨2126409349, 6, [(2, 2), (3, 1), (7, 1), (1609, 1), (15733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1609
    · exact prime_15733
  · decide +kernel

theorem prime_3595620101 : Nat.Prime 3595620101 := by
  apply nodeValid_prime [2, 5, 29, 907, 1367] ⟨3595620101, 2, [(2, 2), (5, 2), (29, 1), (907, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_907
    · exact prime_1367
  · decide +kernel

theorem prime_4176362581 : Nat.Prime 4176362581 := by
  apply nodeValid_prime [2, 3, 5, 13, 5354311] ⟨4176362581, 26, [(2, 2), (3, 1), (5, 1), (13, 1), (5354311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_5354311
  · decide +kernel

theorem prime_5603711327 : Nat.Prime 5603711327 := by
  apply nodeValid_prime [2, 17, 41, 4019879] ⟨5603711327, 5, [(2, 1), (17, 1), (41, 1), (4019879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_4019879
  · decide +kernel

theorem prime_5763933191 : Nat.Prime 5763933191 := by
  apply nodeValid_prime [2, 5, 131, 167, 26347] ⟨5763933191, 7, [(2, 1), (5, 1), (131, 1), (167, 1), (26347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_167
    · exact prime_26347
  · decide +kernel

theorem prime_6879114317 : Nat.Prime 6879114317 := by
  apply nodeValid_prime [2, 41, 67, 107, 5851] ⟨6879114317, 2, [(2, 2), (41, 1), (67, 1), (107, 1), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_67
    · exact prime_107
    · exact prime_5851
  · decide +kernel

theorem prime_8531027003 : Nat.Prime 8531027003 := by
  apply nodeValid_prime [2, 59, 72296839] ⟨8531027003, 2, [(2, 1), (59, 1), (72296839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_72296839
  · decide +kernel

theorem prime_8586018941 : Nat.Prime 8586018941 := by
  apply nodeValid_prime [2, 5, 429300947] ⟨8586018941, 2, [(2, 2), (5, 1), (429300947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_429300947
  · decide +kernel

theorem prime_9675008621 : Nat.Prime 9675008621 := by
  apply nodeValid_prime [2, 5, 19, 41, 563, 1103] ⟨9675008621, 2, [(2, 2), (5, 1), (19, 1), (41, 1), (563, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_563
    · exact prime_1103
  · decide +kernel

theorem prime_10706532973 : Nat.Prime 10706532973 := by
  apply nodeValid_prime [2, 3, 37, 24113813] ⟨10706532973, 5, [(2, 2), (3, 1), (37, 1), (24113813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_24113813
  · decide +kernel

theorem prime_13844157487 : Nat.Prime 13844157487 := by
  apply nodeValid_prime [2, 3, 29443, 78367] ⟨13844157487, 3, [(2, 1), (3, 1), (29443, 1), (78367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29443
    · exact prime_78367
  · decide +kernel

theorem prime_17459184187 : Nat.Prime 17459184187 := by
  apply nodeValid_prime [2, 3, 29, 787, 42499] ⟨17459184187, 2, [(2, 1), (3, 2), (29, 1), (787, 1), (42499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_787
    · exact prime_42499
  · decide +kernel

theorem prime_42251225729 : Nat.Prime 42251225729 := by
  apply nodeValid_prime [2, 330087701] ⟨42251225729, 3, [(2, 7), (330087701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_330087701
  · decide +kernel

theorem prime_59508767893 : Nat.Prime 59508767893 := by
  apply nodeValid_prime [2, 3, 7, 61, 11613733] ⟨59508767893, 2, [(2, 2), (3, 1), (7, 1), (61, 1), (11613733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_11613733
  · decide +kernel

theorem prime_93400895333 : Nat.Prime 93400895333 := by
  apply nodeValid_prime [2, 53, 109, 4041929] ⟨93400895333, 2, [(2, 2), (53, 1), (109, 1), (4041929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_109
    · exact prime_4041929
  · decide +kernel

theorem prime_117057544753 : Nat.Prime 117057544753 := by
  apply nodeValid_prime [2, 3, 19, 4027, 31873] ⟨117057544753, 5, [(2, 4), (3, 1), (19, 1), (4027, 1), (31873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_4027
    · exact prime_31873
  · decide +kernel

theorem prime_154548340939 : Nat.Prime 154548340939 := by
  apply nodeValid_prime [2, 3, 8586018941] ⟨154548340939, 2, [(2, 1), (3, 2), (8586018941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8586018941
  · decide +kernel

theorem prime_199620410833 : Nat.Prime 199620410833 := by
  apply nodeValid_prime [2, 3, 1386252853] ⟨199620410833, 5, [(2, 4), (3, 2), (1386252853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1386252853
  · decide +kernel

theorem prime_417554786141 : Nat.Prime 417554786141 := by
  apply nodeValid_prime [2, 5, 2879, 7251733] ⟨417554786141, 2, [(2, 2), (5, 1), (2879, 1), (7251733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2879
    · exact prime_7251733
  · decide +kernel

theorem prime_1050760085777 : Nat.Prime 1050760085777 := by
  apply nodeValid_prime [2, 137, 8423, 56911] ⟨1050760085777, 3, [(2, 4), (137, 1), (8423, 1), (56911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_8423
    · exact prime_56911
  · decide +kernel

theorem prime_1395510022867 : Nat.Prime 1395510022867 := by
  apply nodeValid_prime [2, 3, 41, 43, 131925697] ⟨1395510022867, 3, [(2, 1), (3, 1), (41, 1), (43, 1), (131925697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_43
    · exact prime_131925697
  · decide +kernel

theorem prime_2086402605907 : Nat.Prime 2086402605907 := by
  apply nodeValid_prime [2, 3, 230393, 1509307] ⟨2086402605907, 2, [(2, 1), (3, 1), (230393, 1), (1509307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_230393
    · exact prime_1509307
  · decide +kernel

theorem prime_2107035822019 : Nat.Prime 2107035822019 := by
  apply nodeValid_prime [2, 3, 269, 1373, 950819] ⟨2107035822019, 3, [(2, 1), (3, 1), (269, 1), (1373, 1), (950819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_1373
    · exact prime_950819
  · decide +kernel

theorem prime_4211312009711 : Nat.Prime 4211312009711 := by
  apply nodeValid_prime [2, 5, 13, 67, 483503101] ⟨4211312009711, 7, [(2, 1), (5, 1), (13, 1), (67, 1), (483503101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_67
    · exact prime_483503101
  · decide +kernel

theorem prime_8329169814421 : Nat.Prime 8329169814421 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 1063, 1435079] ⟨8329169814421, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (1063, 1), (1435079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_1063
    · exact prime_1435079
  · decide +kernel

theorem prime_8329169816447 : Nat.Prime 8329169816447 := by
  apply nodeValid_prime [2, 239, 3467, 5025971] ⟨8329169816447, 5, [(2, 1), (239, 1), (3467, 1), (5025971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_3467
    · exact prime_5025971
  · decide +kernel

theorem prime_8329169816479 : Nat.Prime 8329169816479 := by
  apply nodeValid_prime [2, 3, 7, 19, 47, 74025221] ⟨8329169816479, 3, [(2, 1), (3, 2), (7, 1), (19, 1), (47, 1), (74025221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_47
    · exact prime_74025221
  · decide +kernel

theorem prime_8334647394119 : Nat.Prime 8334647394119 := by
  apply nodeValid_prime [2, 19, 61, 3595620101] ⟨8334647394119, 7, [(2, 1), (19, 1), (61, 1), (3595620101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
    · exact prime_3595620101
  · decide +kernel

theorem prime_8334647394187 : Nat.Prime 8334647394187 := by
  apply nodeValid_prime [2, 3, 241, 5763933191] ⟨8334647394187, 2, [(2, 1), (3, 1), (241, 1), (5763933191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_5763933191
  · decide +kernel

theorem prime_8334647571101 : Nat.Prime 8334647571101 := by
  apply nodeValid_prime [2, 5, 41, 1489, 1365239] ⟨8334647571101, 7, [(2, 2), (5, 2), (41, 1), (1489, 1), (1365239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_1489
    · exact prime_1365239
  · decide +kernel

theorem prime_8340127768673 : Nat.Prime 8340127768673 := by
  apply nodeValid_prime [2, 7, 19, 251, 1889, 4133] ⟨8340127768673, 3, [(2, 5), (7, 1), (19, 1), (251, 1), (1889, 1), (4133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_251
    · exact prime_1889
    · exact prime_4133
  · decide +kernel

theorem prime_8340127787837 : Nat.Prime 8340127787837 := by
  apply nodeValid_prime [2, 13, 941, 170443223] ⟨8340127787837, 2, [(2, 2), (13, 1), (941, 1), (170443223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_941
    · exact prime_170443223
  · decide +kernel

theorem prime_8340127788329 : Nat.Prime 8340127788329 := by
  apply nodeValid_prime [2, 7, 37, 71, 56692369] ⟨8340127788329, 3, [(2, 3), (7, 1), (37, 1), (71, 1), (56692369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_71
    · exact prime_56692369
  · decide +kernel

theorem prime_8345610410707 : Nat.Prime 8345610410707 := by
  apply nodeValid_prime [2, 3, 154548340939] ⟨8345610410707, 3, [(2, 1), (3, 3), (154548340939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_154548340939
  · decide +kernel

theorem prime_8345610423389 : Nat.Prime 8345610423389 := by
  apply nodeValid_prime [2, 7, 29, 26981, 380929] ⟨8345610423389, 2, [(2, 2), (7, 1), (29, 1), (26981, 1), (380929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_26981
    · exact prime_380929
  · decide +kernel

theorem prime_8345610423629 : Nat.Prime 8345610423629 := by
  apply nodeValid_prime [2, 2086402605907] ⟨8345610423629, 2, [(2, 2), (2086402605907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2086402605907
  · decide +kernel

theorem prime_8351095489901 : Nat.Prime 8351095489901 := by
  apply nodeValid_prime [2, 5, 94889, 880091] ⟨8351095489901, 2, [(2, 2), (5, 2), (94889, 1), (880091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_94889
    · exact prime_880091
  · decide +kernel

theorem prime_8351095718941 : Nat.Prime 8351095718941 := by
  apply nodeValid_prime [2, 3, 5, 13, 10706532973] ⟨8351095718941, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (10706532973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_10706532973
  · decide +kernel

theorem prime_8351095722821 : Nat.Prime 8351095722821 := by
  apply nodeValid_prime [2, 5, 417554786141] ⟨8351095722821, 3, [(2, 2), (5, 1), (417554786141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_417554786141
  · decide +kernel

theorem prime_8356583006423 : Nat.Prime 8356583006423 := by
  apply nodeValid_prime [2, 7, 73, 173, 47264137] ⟨8356583006423, 5, [(2, 1), (7, 1), (73, 1), (173, 1), (47264137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_173
    · exact prime_47264137
  · decide +kernel

theorem prime_8356583095477 : Nat.Prime 8356583095477 := by
  apply nodeValid_prime [2, 3, 7, 11, 67, 89, 761, 1993] ⟨8356583095477, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (67, 1), (89, 1), (761, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_67
    · exact prime_89
    · exact prime_761
    · exact prime_1993
  · decide +kernel

theorem prime_8356583097407 : Nat.Prime 8356583097407 := by
  apply nodeValid_prime [2, 4127, 1012428289] ⟨8356583097407, 5, [(2, 1), (4127, 1), (1012428289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4127
    · exact prime_1012428289
  · decide +kernel

theorem prime_8362072972321 : Nat.Prime 8362072972321 := by
  apply nodeValid_prime [2, 3, 5, 20393, 854263] ⟨8362072972321, 7, [(2, 5), (3, 1), (5, 1), (20393, 1), (854263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_20393
    · exact prime_854263
  · decide +kernel

theorem prime_8362073067079 : Nat.Prime 8362073067079 := by
  apply nodeValid_prime [2, 3, 1423, 3709, 264059] ⟨8362073067079, 3, [(2, 1), (3, 1), (1423, 1), (3709, 1), (264059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1423
    · exact prime_3709
    · exact prime_264059
  · decide +kernel

theorem prime_8362073067701 : Nat.Prime 8362073067701 := by
  apply nodeValid_prime [2, 5, 11, 50909, 149323] ⟨8362073067701, 2, [(2, 2), (5, 2), (11, 1), (50909, 1), (149323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_50909
    · exact prime_149323
  · decide +kernel

theorem prime_8367565352527 : Nat.Prime 8367565352527 := by
  apply nodeValid_prime [2, 3, 29, 43, 11177, 33353] ⟨8367565352527, 3, [(2, 1), (3, 2), (29, 1), (43, 1), (11177, 1), (33353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
    · exact prime_11177
    · exact prime_33353
  · decide +kernel

theorem prime_8367565353131 : Nat.Prime 8367565353131 := by
  apply nodeValid_prime [2, 5, 215279, 3886847] ⟨8367565353131, 2, [(2, 1), (5, 1), (215279, 1), (3886847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_215279
    · exact prime_3886847
  · decide +kernel

theorem prime_8367565380583 : Nat.Prime 8367565380583 := by
  apply nodeValid_prime [2, 3, 41, 9941, 3421637] ⟨8367565380583, 3, [(2, 1), (3, 1), (41, 1), (9941, 1), (3421637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_9941
    · exact prime_3421637
  · decide +kernel

theorem prime_8373060137203 : Nat.Prime 8373060137203 := by
  apply nodeValid_prime [2, 3, 1395510022867] ⟨8373060137203, 2, [(2, 1), (3, 1), (1395510022867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1395510022867
  · decide +kernel

theorem prime_8373060138067 : Nat.Prime 8373060138067 := by
  apply nodeValid_prime [2, 3, 13, 17, 89, 1171, 60589] ⟨8373060138067, 11, [(2, 1), (3, 1), (13, 1), (17, 1), (89, 1), (1171, 1), (60589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_89
    · exact prime_1171
    · exact prime_60589
  · decide +kernel

theorem prime_8373060227869 : Nat.Prime 8373060227869 := by
  apply nodeValid_prime [2, 3, 7, 31, 5701, 564017] ⟨8373060227869, 6, [(2, 2), (3, 1), (7, 1), (31, 1), (5701, 1), (564017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_5701
    · exact prime_564017
  · decide +kernel

theorem prime_8378557465787 : Nat.Prime 8378557465787 := by
  apply nodeValid_prime [2, 433, 9675008621] ⟨8378557465787, 2, [(2, 1), (433, 1), (9675008621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_433
    · exact prime_9675008621
  · decide +kernel

theorem prime_8378557466969 : Nat.Prime 8378557466969 := by
  apply nodeValid_prime [2, 13, 229, 351803723] ⟨8378557466969, 3, [(2, 3), (13, 1), (229, 1), (351803723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_229
    · exact prime_351803723
  · decide +kernel

theorem prime_8378557517521 : Nat.Prime 8378557517521 := by
  apply nodeValid_prime [2, 3, 5, 17, 684522673] ⟨8378557517521, 46, [(2, 4), (3, 2), (5, 1), (17, 1), (684522673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_684522673
  · decide +kernel

theorem prime_8384057192143 : Nat.Prime 8384057192143 := by
  apply nodeValid_prime [2, 3, 617, 251637469] ⟨8384057192143, 3, [(2, 1), (3, 3), (617, 1), (251637469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_617
    · exact prime_251637469
  · decide +kernel

theorem prime_8384057192941 : Nat.Prime 8384057192941 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 23, 61, 696481] ⟨8384057192941, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (23, 1), (61, 1), (696481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_61
    · exact prime_696481
  · decide +kernel

theorem prime_8384057254987 : Nat.Prime 8384057254987 := by
  apply nodeValid_prime [2, 3, 7, 199620410833] ⟨8384057254987, 5, [(2, 1), (3, 1), (7, 1), (199620410833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199620410833
  · decide +kernel

theorem prime_8389559437123 : Nat.Prime 8389559437123 := by
  apply nodeValid_prime [2, 3, 101, 13844157487] ⟨8389559437123, 7, [(2, 1), (3, 1), (101, 1), (13844157487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_13844157487
  · decide +kernel

theorem prime_8389559485297 : Nat.Prime 8389559485297 := by
  apply nodeValid_prime [2, 3, 11, 19, 757, 368243] ⟨8389559485297, 5, [(2, 4), (3, 2), (11, 1), (19, 1), (757, 1), (368243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_757
    · exact prime_368243
  · decide +kernel

theorem prime_8389559485763 : Nat.Prime 8389559485763 := by
  apply nodeValid_prime [2, 7, 13, 1223, 37691317] ⟨8389559485763, 2, [(2, 1), (7, 1), (13, 1), (1223, 1), (37691317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1223
    · exact prime_37691317
  · decide +kernel

theorem prime_8395064074997 : Nat.Prime 8395064074997 := by
  apply nodeValid_prime [2, 17483, 120046103] ⟨8395064074997, 2, [(2, 2), (17483, 1), (120046103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17483
    · exact prime_120046103
  · decide +kernel

theorem prime_8395064107789 : Nat.Prime 8395064107789 := by
  apply nodeValid_prime [2, 3, 53, 2113, 6246941] ⟨8395064107789, 2, [(2, 2), (3, 1), (53, 1), (2113, 1), (6246941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_2113
    · exact prime_6246941
  · decide +kernel

theorem prime_8395064109853 : Nat.Prime 8395064109853 := by
  apply nodeValid_prime [2, 3, 7, 47, 2126409349] ⟨8395064109853, 2, [(2, 2), (3, 1), (7, 1), (47, 1), (2126409349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_2126409349
  · decide +kernel

theorem prime_8400571028309 : Nat.Prime 8400571028309 := by
  apply nodeValid_prime [2, 1747, 1202142391] ⟨8400571028309, 2, [(2, 2), (1747, 1), (1202142391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1747
    · exact prime_1202142391
  · decide +kernel

theorem prime_8400571029769 : Nat.Prime 8400571029769 := by
  apply nodeValid_prime [2, 3, 37, 107, 88412173] ⟨8400571029769, 11, [(2, 3), (3, 1), (37, 1), (107, 1), (88412173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_107
    · exact prime_88412173
  · decide +kernel

theorem prime_8400571155311 : Nat.Prime 8400571155311 := by
  apply nodeValid_prime [2, 5, 17, 137, 360694339] ⟨8400571155311, 11, [(2, 1), (5, 1), (17, 1), (137, 1), (360694339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_137
    · exact prime_360694339
  · decide +kernel

theorem prime_8406080579971 : Nat.Prime 8406080579971 := by
  apply nodeValid_prime [2, 3, 5, 93400895333] ⟨8406080579971, 2, [(2, 1), (3, 2), (5, 1), (93400895333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_93400895333
  · decide +kernel

theorem prime_8406080580217 : Nat.Prime 8406080580217 := by
  apply nodeValid_prime [2, 3, 11, 17, 151, 211, 58787] ⟨8406080580217, 5, [(2, 3), (3, 1), (11, 1), (17, 1), (151, 1), (211, 1), (58787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_151
    · exact prime_211
    · exact prime_58787
  · decide +kernel

theorem prime_8406080686217 : Nat.Prime 8406080686217 := by
  apply nodeValid_prime [2, 1050760085777] ⟨8406080686217, 3, [(2, 3), (1050760085777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1050760085777
  · decide +kernel

theorem prime_8411592623633 : Nat.Prime 8411592623633 := by
  apply nodeValid_prime [2, 11, 17, 743, 3783797] ⟨8411592623633, 3, [(2, 4), (11, 1), (17, 1), (743, 1), (3783797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_743
    · exact prime_3783797
  · decide +kernel

theorem prime_8411592624959 : Nat.Prime 8411592624959 := by
  apply nodeValid_prime [2, 17, 29, 8531027003] ⟨8411592624959, 31, [(2, 1), (17, 1), (29, 1), (8531027003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_8531027003
  · decide +kernel

theorem prime_8411592661861 : Nat.Prime 8411592661861 := by
  apply nodeValid_prime [2, 3, 5, 571, 1567, 156683] ⟨8411592661861, 2, [(2, 2), (3, 1), (5, 1), (571, 1), (1567, 1), (156683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_571
    · exact prime_1567
    · exact prime_156683
  · decide +kernel

theorem prime_8417107085081 : Nat.Prime 8417107085081 := by
  apply nodeValid_prime [2, 5, 39367, 5345281] ⟨8417107085081, 6, [(2, 3), (5, 1), (39367, 1), (5345281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_39367
    · exact prime_5345281
  · decide +kernel

theorem prime_8417107200871 : Nat.Prime 8417107200871 := by
  apply nodeValid_prime [2, 3, 5, 43, 43481, 50021] ⟨8417107200871, 3, [(2, 1), (3, 2), (5, 1), (43, 1), (43481, 1), (50021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_43481
    · exact prime_50021
  · decide +kernel

theorem prime_8417107201117 : Nat.Prime 8417107201117 := by
  apply nodeValid_prime [2, 3, 19, 4093, 9019579] ⟨8417107201117, 2, [(2, 2), (3, 1), (19, 1), (4093, 1), (9019579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_4093
    · exact prime_9019579
  · decide +kernel

theorem prime_8422623965941 : Nat.Prime 8422623965941 := by
  apply nodeValid_prime [2, 3, 5, 83, 239, 1451, 4877] ⟨8422623965941, 2, [(2, 2), (3, 1), (5, 1), (83, 1), (239, 1), (1451, 1), (4877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_239
    · exact prime_1451
    · exact prime_4877
  · decide +kernel

theorem prime_8422624017391 : Nat.Prime 8422624017391 := by
  apply nodeValid_prime [2, 3, 5, 11, 12511, 2040053] ⟨8422624017391, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (12511, 1), (2040053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_12511
    · exact prime_2040053
  · decide +kernel

theorem prime_8422624019423 : Nat.Prime 8422624019423 := by
  apply nodeValid_prime [2, 4211312009711] ⟨8422624019423, 5, [(2, 1), (4211312009711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4211312009711
  · decide +kernel

theorem prime_8428143222217 : Nat.Prime 8428143222217 := by
  apply nodeValid_prime [2, 3, 117057544753] ⟨8428143222217, 7, [(2, 3), (3, 2), (117057544753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_117057544753
  · decide +kernel

theorem prime_8428143222347 : Nat.Prime 8428143222347 := by
  apply nodeValid_prime [2, 37, 4513, 25236833] ⟨8428143222347, 2, [(2, 1), (37, 1), (4513, 1), (25236833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_4513
    · exact prime_25236833
  · decide +kernel

theorem prime_8428143288077 : Nat.Prime 8428143288077 := by
  apply nodeValid_prime [2, 2107035822019] ⟨8428143288077, 2, [(2, 2), (2107035822019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2107035822019
  · decide +kernel

theorem prime_8433665048957 : Nat.Prime 8433665048957 := by
  apply nodeValid_prime [2, 7, 271, 5717, 27773] ⟨8433665048957, 3, [(2, 2), (7, 2), (271, 1), (5717, 1), (27773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_271
    · exact prime_5717
    · exact prime_27773
  · decide +kernel

theorem prime_8433665088911 : Nat.Prime 8433665088911 := by
  apply nodeValid_prime [2, 5, 41, 79, 337, 877, 881] ⟨8433665088911, 29, [(2, 1), (5, 1), (41, 1), (79, 1), (337, 1), (877, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_79
    · exact prime_337
    · exact prime_877
    · exact prime_881
  · decide +kernel

theorem prime_8433665089061 : Nat.Prime 8433665089061 := by
  apply nodeValid_prime [2, 5, 163, 1823, 1419097] ⟨8433665089061, 2, [(2, 2), (5, 1), (163, 1), (1823, 1), (1419097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_1823
    · exact prime_1419097
  · decide +kernel

theorem prime_8439189203987 : Nat.Prime 8439189203987 := by
  apply nodeValid_prime [2, 31, 277, 491393339] ⟨8439189203987, 2, [(2, 1), (31, 1), (277, 1), (491393339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_277
    · exact prime_491393339
  · decide +kernel

theorem prime_8439189204923 : Nat.Prime 8439189204923 := by
  apply nodeValid_prime [2, 7, 47, 47381, 270689] ⟨8439189204923, 2, [(2, 1), (7, 1), (47, 1), (47381, 1), (270689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_47
    · exact prime_47381
    · exact prime_270689
  · decide +kernel

theorem prime_8439189258463 : Nat.Prime 8439189258463 := by
  apply nodeValid_prime [2, 3, 251, 5603711327] ⟨8439189258463, 3, [(2, 1), (3, 1), (251, 1), (5603711327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_5603711327
  · decide +kernel

theorem prime_8444715829603 : Nat.Prime 8444715829603 := by
  apply nodeValid_prime [2, 3, 13, 307, 352656637] ⟨8444715829603, 2, [(2, 1), (3, 1), (13, 1), (307, 1), (352656637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_307
    · exact prime_352656637
  · decide +kernel

theorem prime_8444715829831 : Nat.Prime 8444715829831 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 47, 3089, 5431] ⟨8444715829831, 7, [(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (47, 1), (3089, 1), (5431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_47
    · exact prime_3089
    · exact prime_5431
  · decide +kernel

theorem prime_8444715928433 : Nat.Prime 8444715928433 := by
  apply nodeValid_prime [2, 7, 59, 1277953379] ⟨8444715928433, 3, [(2, 4), (7, 1), (59, 1), (1277953379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_1277953379
  · decide +kernel

theorem prime_8450245040807 : Nat.Prime 8450245040807 := by
  apply nodeValid_prime [2, 71, 59508767893] ⟨8450245040807, 5, [(2, 1), (71, 1), (59508767893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_59508767893
  · decide +kernel

theorem prime_8450245145801 : Nat.Prime 8450245145801 := by
  apply nodeValid_prime [2, 5, 42251225729] ⟨8450245145801, 3, [(2, 3), (5, 2), (42251225729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_42251225729
  · decide +kernel

theorem prime_8450245146509 : Nat.Prime 8450245146509 := by
  apply nodeValid_prime [2, 11, 17459184187] ⟨8450245146509, 2, [(2, 2), (11, 2), (17459184187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17459184187
  · decide +kernel

theorem prime_8455776546289 : Nat.Prime 8455776546289 := by
  apply nodeValid_prime [2, 3, 227, 3779, 205357] ⟨8455776546289, 11, [(2, 4), (3, 1), (227, 1), (3779, 1), (205357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_3779
    · exact prime_205357
  · decide +kernel

theorem prime_8455776547573 : Nat.Prime 8455776547573 := by
  apply nodeValid_prime [2, 3, 71, 2657, 1245091] ⟨8455776547573, 5, [(2, 2), (3, 2), (71, 1), (2657, 1), (1245091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_2657
    · exact prime_1245091
  · decide +kernel

theorem prime_8455776602459 : Nat.Prime 8455776602459 := by
  apply nodeValid_prime [2, 17, 80473, 3090469] ⟨8455776602459, 2, [(2, 1), (17, 1), (80473, 1), (3090469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_80473
    · exact prime_3090469
  · decide +kernel

theorem prime_8461310589107 : Nat.Prime 8461310589107 := by
  apply nodeValid_prime [2, 1013, 4176362581] ⟨8461310589107, 2, [(2, 1), (1013, 1), (4176362581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1013
    · exact prime_4176362581
  · decide +kernel

theorem prime_8461310589577 : Nat.Prime 8461310589577 := by
  apply nodeValid_prime [2, 3, 13, 17, 23, 7706617] ⟨8461310589577, 5, [(2, 3), (3, 3), (13, 1), (17, 1), (23, 1), (7706617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_23
    · exact prime_7706617
  · decide +kernel

theorem prime_8461310609911 : Nat.Prime 8461310609911 := by
  apply nodeValid_prime [2, 3, 5, 41, 6879114317] ⟨8461310609911, 3, [(2, 1), (3, 1), (5, 1), (41, 1), (6879114317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_6879114317
  · decide +kernel

end Sude.Lucas.Generated
