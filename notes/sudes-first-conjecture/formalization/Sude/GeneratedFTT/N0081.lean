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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0080

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_4253 : Nat.Prime 4253 := by
  apply nodeValid_prime [2, 1063] ⟨4253, 2, [(2, 2), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1063
  · decide +kernel

theorem prime_6199 : Nat.Prime 6199 := by
  apply nodeValid_prime [2, 3, 1033] ⟨6199, 3, [(2, 1), (3, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1033
  · decide +kernel

theorem prime_16937 : Nat.Prime 16937 := by
  apply nodeValid_prime [2, 29, 73] ⟨16937, 3, [(2, 3), (29, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_73
  · decide +kernel

theorem prime_18287 : Nat.Prime 18287 := by
  apply nodeValid_prime [2, 41, 223] ⟨18287, 5, [(2, 1), (41, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_223
  · decide +kernel

theorem prime_19333 : Nat.Prime 19333 := by
  apply nodeValid_prime [2, 3, 179] ⟨19333, 2, [(2, 2), (3, 3), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
  · decide +kernel

theorem prime_21319 : Nat.Prime 21319 := by
  apply nodeValid_prime [2, 3, 11, 17, 19] ⟨21319, 14, [(2, 1), (3, 1), (11, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_24251 : Nat.Prime 24251 := by
  apply nodeValid_prime [2, 5, 97] ⟨24251, 6, [(2, 1), (5, 3), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_28657 : Nat.Prime 28657 := by
  apply nodeValid_prime [2, 3, 199] ⟨28657, 5, [(2, 4), (3, 2), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
  · decide +kernel

theorem prime_33601 : Nat.Prime 33601 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨33601, 29, [(2, 6), (3, 1), (5, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_34729 : Nat.Prime 34729 := by
  apply nodeValid_prime [2, 3, 1447] ⟨34729, 13, [(2, 3), (3, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1447
  · decide +kernel

theorem prime_38803 : Nat.Prime 38803 := by
  apply nodeValid_prime [2, 3, 29, 223] ⟨38803, 5, [(2, 1), (3, 1), (29, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_223
  · decide +kernel

theorem prime_44771 : Nat.Prime 44771 := by
  apply nodeValid_prime [2, 5, 11, 37] ⟨44771, 6, [(2, 1), (5, 1), (11, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_49667 : Nat.Prime 49667 := by
  apply nodeValid_prime [2, 19, 1307] ⟨49667, 2, [(2, 1), (19, 1), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1307
  · decide +kernel

theorem prime_51349 : Nat.Prime 51349 := by
  apply nodeValid_prime [2, 3, 11, 389] ⟨51349, 10, [(2, 2), (3, 1), (11, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_389
  · decide +kernel

theorem prime_53731 : Nat.Prime 53731 := by
  apply nodeValid_prime [2, 3, 5, 199] ⟨53731, 12, [(2, 1), (3, 3), (5, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
  · decide +kernel

theorem prime_55469 : Nat.Prime 55469 := by
  apply nodeValid_prime [2, 7, 283] ⟨55469, 2, [(2, 2), (7, 2), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_283
  · decide +kernel

theorem prime_58321 : Nat.Prime 58321 := by
  apply nodeValid_prime [2, 3, 5] ⟨58321, 11, [(2, 4), (3, 6), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_68699 : Nat.Prime 68699 := by
  apply nodeValid_prime [2, 7, 701] ⟨68699, 2, [(2, 1), (7, 2), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_701
  · decide +kernel

theorem prime_76771 : Nat.Prime 76771 := by
  apply nodeValid_prime [2, 3, 5, 853] ⟨76771, 2, [(2, 1), (3, 2), (5, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_853
  · decide +kernel

theorem prime_89293 : Nat.Prime 89293 := by
  apply nodeValid_prime [2, 3, 7, 1063] ⟨89293, 5, [(2, 2), (3, 1), (7, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1063
  · decide +kernel

theorem prime_95957 : Nat.Prime 95957 := by
  apply nodeValid_prime [2, 7, 23, 149] ⟨95957, 2, [(2, 2), (7, 1), (23, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_149
  · decide +kernel

theorem prime_101891 : Nat.Prime 101891 := by
  apply nodeValid_prime [2, 5, 23, 443] ⟨101891, 2, [(2, 1), (5, 1), (23, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_443
  · decide +kernel

theorem prime_108131 : Nat.Prime 108131 := by
  apply nodeValid_prime [2, 5, 11, 983] ⟨108131, 6, [(2, 1), (5, 1), (11, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_983
  · decide +kernel

theorem prime_110939 : Nat.Prime 110939 := by
  apply nodeValid_prime [2, 55469] ⟨110939, 2, [(2, 1), (55469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_55469
  · decide +kernel

theorem prime_111043 : Nat.Prime 111043 := by
  apply nodeValid_prime [2, 3, 31, 199] ⟨111043, 2, [(2, 1), (3, 2), (31, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_199
  · decide +kernel

theorem prime_117703 : Nat.Prime 117703 := by
  apply nodeValid_prime [2, 3, 13, 503] ⟨117703, 3, [(2, 1), (3, 2), (13, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_503
  · decide +kernel

theorem prime_135497 : Nat.Prime 135497 := by
  apply nodeValid_prime [2, 16937] ⟨135497, 3, [(2, 3), (16937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16937
  · decide +kernel

theorem prime_137699 : Nat.Prime 137699 := by
  apply nodeValid_prime [2, 11, 569] ⟨137699, 2, [(2, 1), (11, 2), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_569
  · decide +kernel

theorem prime_149269 : Nat.Prime 149269 := by
  apply nodeValid_prime [2, 3, 7, 1777] ⟨149269, 2, [(2, 2), (3, 1), (7, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1777
  · decide +kernel

theorem prime_211469 : Nat.Prime 211469 := by
  apply nodeValid_prime [2, 29, 1823] ⟨211469, 2, [(2, 2), (29, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1823
  · decide +kernel

theorem prime_216379 : Nat.Prime 216379 := by
  apply nodeValid_prime [2, 3, 4007] ⟨216379, 2, [(2, 1), (3, 3), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4007
  · decide +kernel

theorem prime_245561 : Nat.Prime 245561 := by
  apply nodeValid_prime [2, 5, 7, 877] ⟨245561, 3, [(2, 3), (5, 1), (7, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_877
  · decide +kernel

theorem prime_266089 : Nat.Prime 266089 := by
  apply nodeValid_prime [2, 3, 11087] ⟨266089, 7, [(2, 3), (3, 1), (11087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11087
  · decide +kernel

theorem prime_269683 : Nat.Prime 269683 := by
  apply nodeValid_prime [2, 3, 7, 6421] ⟨269683, 7, [(2, 1), (3, 1), (7, 1), (6421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6421
  · decide +kernel

theorem prime_286609 : Nat.Prime 286609 := by
  apply nodeValid_prime [2, 3, 7, 853] ⟨286609, 13, [(2, 4), (3, 1), (7, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_853
  · decide +kernel

theorem prime_321949 : Nat.Prime 321949 := by
  apply nodeValid_prime [2, 3, 11, 271] ⟨321949, 2, [(2, 2), (3, 3), (11, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_271
  · decide +kernel

theorem prime_340577 : Nat.Prime 340577 := by
  apply nodeValid_prime [2, 29, 367] ⟨340577, 3, [(2, 5), (29, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_367
  · decide +kernel

theorem prime_348191 : Nat.Prime 348191 := by
  apply nodeValid_prime [2, 5, 34819] ⟨348191, 7, [(2, 1), (5, 1), (34819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_34819
  · decide +kernel

theorem prime_367889 : Nat.Prime 367889 := by
  apply nodeValid_prime [2, 22993] ⟨367889, 3, [(2, 4), (22993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_22993
  · decide +kernel

theorem prime_390763 : Nat.Prime 390763 := by
  apply nodeValid_prime [2, 3, 17, 1277] ⟨390763, 3, [(2, 1), (3, 2), (17, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1277
  · decide +kernel

theorem prime_411941 : Nat.Prime 411941 := by
  apply nodeValid_prime [2, 5, 43, 479] ⟨411941, 2, [(2, 2), (5, 1), (43, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_479
  · decide +kernel

theorem prime_416401 : Nat.Prime 416401 := by
  apply nodeValid_prime [2, 3, 5, 347] ⟨416401, 17, [(2, 4), (3, 1), (5, 2), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_347
  · decide +kernel

theorem prime_468001 : Nat.Prime 468001 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨468001, 11, [(2, 5), (3, 2), (5, 3), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_477517 : Nat.Prime 477517 := by
  apply nodeValid_prime [2, 3, 13, 3061] ⟨477517, 2, [(2, 2), (3, 1), (13, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3061
  · decide +kernel

theorem prime_478441 : Nat.Prime 478441 := by
  apply nodeValid_prime [2, 3, 5, 443] ⟨478441, 14, [(2, 3), (3, 3), (5, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_443
  · decide +kernel

theorem prime_598463 : Nat.Prime 598463 := by
  apply nodeValid_prime [2, 19, 15749] ⟨598463, 5, [(2, 1), (19, 1), (15749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_15749
  · decide +kernel

theorem prime_854593 : Nat.Prime 854593 := by
  apply nodeValid_prime [2, 3, 4451] ⟨854593, 5, [(2, 6), (3, 1), (4451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4451
  · decide +kernel

theorem prime_936007 : Nat.Prime 936007 := by
  apply nodeValid_prime [2, 3, 73, 2137] ⟨936007, 3, [(2, 1), (3, 1), (73, 1), (2137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_2137
  · decide +kernel

theorem prime_999541 : Nat.Prime 999541 := by
  apply nodeValid_prime [2, 3, 5, 617] ⟨999541, 2, [(2, 2), (3, 4), (5, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_617
  · decide +kernel

theorem prime_1101593 : Nat.Prime 1101593 := by
  apply nodeValid_prime [2, 137699] ⟨1101593, 3, [(2, 3), (137699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_137699
  · decide +kernel

theorem prime_1164091 : Nat.Prime 1164091 := by
  apply nodeValid_prime [2, 3, 5, 38803] ⟨1164091, 3, [(2, 1), (3, 1), (5, 1), (38803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_38803
  · decide +kernel

theorem prime_1376203 : Nat.Prime 1376203 := by
  apply nodeValid_prime [2, 3, 347, 661] ⟨1376203, 2, [(2, 1), (3, 1), (347, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_347
    · exact prime_661
  · decide +kernel

theorem prime_1799393 : Nat.Prime 1799393 := by
  apply nodeValid_prime [2, 7, 29, 277] ⟨1799393, 3, [(2, 5), (7, 1), (29, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_277
  · decide +kernel

theorem prime_2323613 : Nat.Prime 2323613 := by
  apply nodeValid_prime [2, 61, 89, 107] ⟨2323613, 2, [(2, 2), (61, 1), (89, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_89
    · exact prime_107
  · decide +kernel

theorem prime_2435603 : Nat.Prime 2435603 := by
  apply nodeValid_prime [2, 13, 113, 829] ⟨2435603, 2, [(2, 1), (13, 1), (113, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
    · exact prime_829
  · decide +kernel

theorem prime_2630321 : Nat.Prime 2630321 := by
  apply nodeValid_prime [2, 5, 7, 11, 61] ⟨2630321, 3, [(2, 4), (5, 1), (7, 2), (11, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_2808007 : Nat.Prime 2808007 := by
  apply nodeValid_prime [2, 3, 468001] ⟨2808007, 3, [(2, 1), (3, 1), (468001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_468001
  · decide +kernel

theorem prime_2815529 : Nat.Prime 2815529 := by
  apply nodeValid_prime [2, 353, 997] ⟨2815529, 3, [(2, 3), (353, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_997
  · decide +kernel

theorem prime_3156053 : Nat.Prime 3156053 := by
  apply nodeValid_prime [2, 19, 131, 317] ⟨3156053, 2, [(2, 2), (19, 1), (131, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_131
    · exact prime_317
  · decide +kernel

theorem prime_3557273 : Nat.Prime 3557273 := by
  apply nodeValid_prime [2, 23, 19333] ⟨3557273, 3, [(2, 3), (23, 1), (19333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_19333
  · decide +kernel

theorem prime_4354711 : Nat.Prime 4354711 := by
  apply nodeValid_prime [2, 3, 5, 379, 383] ⟨4354711, 3, [(2, 1), (3, 1), (5, 1), (379, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_379
    · exact prime_383
  · decide +kernel

theorem prime_4775171 : Nat.Prime 4775171 := by
  apply nodeValid_prime [2, 5, 477517] ⟨4775171, 2, [(2, 1), (5, 1), (477517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_477517
  · decide +kernel

theorem prime_5260643 : Nat.Prime 5260643 := by
  apply nodeValid_prime [2, 2630321] ⟨5260643, 2, [(2, 1), (2630321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2630321
  · decide +kernel

theorem prime_5763011 : Nat.Prime 5763011 := by
  apply nodeValid_prime [2, 5, 11, 52391] ⟨5763011, 2, [(2, 1), (5, 1), (11, 1), (52391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_52391
  · decide +kernel

theorem prime_6790859 : Nat.Prime 6790859 := by
  apply nodeValid_prime [2, 1373, 2473] ⟨6790859, 2, [(2, 1), (1373, 1), (2473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1373
    · exact prime_2473
  · decide +kernel

theorem prime_7106753 : Nat.Prime 7106753 := by
  apply nodeValid_prime [2, 111043] ⟨7106753, 3, [(2, 6), (111043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_111043
  · decide +kernel

theorem prime_7161493 : Nat.Prime 7161493 := by
  apply nodeValid_prime [2, 3, 13, 29, 1583] ⟨7161493, 2, [(2, 2), (3, 1), (13, 1), (29, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_1583
  · decide +kernel

theorem prime_9634841 : Nat.Prime 9634841 := by
  apply nodeValid_prime [2, 5, 79, 3049] ⟨9634841, 6, [(2, 3), (5, 1), (79, 1), (3049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_3049
  · decide +kernel

theorem prime_11232029 : Nat.Prime 11232029 := by
  apply nodeValid_prime [2, 2808007] ⟨11232029, 2, [(2, 2), (2808007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2808007
  · decide +kernel

theorem prime_15433163 : Nat.Prime 15433163 := by
  apply nodeValid_prime [2, 29, 266089] ⟨15433163, 2, [(2, 1), (29, 1), (266089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_266089
  · decide +kernel

theorem prime_15989251 : Nat.Prime 15989251 := by
  apply nodeValid_prime [2, 3, 5, 21319] ⟨15989251, 2, [(2, 1), (3, 1), (5, 3), (21319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21319
  · decide +kernel

theorem prime_17538151 : Nat.Prime 17538151 := by
  apply nodeValid_prime [2, 3, 5, 7, 16703] ⟨17538151, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (16703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_16703
  · decide +kernel

theorem prime_17993867 : Nat.Prime 17993867 := by
  apply nodeValid_prime [2, 11, 23, 43, 827] ⟨17993867, 2, [(2, 1), (11, 1), (23, 1), (43, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_43
    · exact prime_827
  · decide +kernel

theorem prime_18999131 : Nat.Prime 18999131 := by
  apply nodeValid_prime [2, 5, 37, 51349] ⟨18999131, 2, [(2, 1), (5, 1), (37, 1), (51349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_51349
  · decide +kernel

theorem prime_19269683 : Nat.Prime 19269683 := by
  apply nodeValid_prime [2, 9634841] ⟨19269683, 2, [(2, 1), (9634841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9634841
  · decide +kernel

theorem prime_20364661 : Nat.Prime 20364661 := by
  apply nodeValid_prime [2, 3, 5, 23, 4919] ⟨20364661, 2, [(2, 2), (3, 2), (5, 1), (23, 1), (4919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_4919
  · decide +kernel

theorem prime_25191503 : Nat.Prime 25191503 := by
  apply nodeValid_prime [2, 7, 1799393] ⟨25191503, 7, [(2, 1), (7, 1), (1799393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1799393
  · decide +kernel

theorem prime_25968223 : Nat.Prime 25968223 := by
  apply nodeValid_prime [2, 3, 7, 68699] ⟨25968223, 5, [(2, 1), (3, 3), (7, 1), (68699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_68699
  · decide +kernel

theorem prime_27514027 : Nat.Prime 27514027 := by
  apply nodeValid_prime [2, 3, 23, 22153] ⟨27514027, 2, [(2, 1), (3, 3), (23, 1), (22153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_22153
  · decide +kernel

theorem prime_31198337 : Nat.Prime 31198337 := by
  apply nodeValid_prime [2, 13, 18749] ⟨31198337, 3, [(2, 7), (13, 1), (18749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_18749
  · decide +kernel

theorem prime_39588743 : Nat.Prime 39588743 := by
  apply nodeValid_prime [2, 19, 37, 761] ⟨39588743, 5, [(2, 1), (19, 1), (37, 2), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_761
  · decide +kernel

theorem prime_42444811 : Nat.Prime 42444811 := by
  apply nodeValid_prime [2, 3, 5, 17467] ⟨42444811, 14, [(2, 1), (3, 5), (5, 1), (17467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17467
  · decide +kernel

theorem prime_49533571 : Nat.Prime 49533571 := by
  apply nodeValid_prime [2, 3, 5, 19, 83, 349] ⟨49533571, 10, [(2, 1), (3, 2), (5, 1), (19, 1), (83, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_83
    · exact prime_349
  · decide +kernel

theorem prime_50383007 : Nat.Prime 50383007 := by
  apply nodeValid_prime [2, 25191503] ⟨50383007, 5, [(2, 1), (25191503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25191503
  · decide +kernel

theorem prime_55041479 : Nat.Prime 55041479 := by
  apply nodeValid_prime [2, 17, 29, 55823] ⟨55041479, 11, [(2, 1), (17, 1), (29, 1), (55823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_55823
  · decide +kernel

theorem prime_142202971 : Nat.Prime 142202971 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 97, 179] ⟨142202971, 11, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (97, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_97
    · exact prime_179
  · decide +kernel

theorem prime_185319721 : Nat.Prime 185319721 := by
  apply nodeValid_prime [2, 3, 5, 17, 107, 283] ⟨185319721, 7, [(2, 3), (3, 2), (5, 1), (17, 1), (107, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_107
    · exact prime_283
  · decide +kernel

theorem prime_187190023 : Nat.Prime 187190023 := by
  apply nodeValid_prime [2, 3, 31198337] ⟨187190023, 3, [(2, 1), (3, 1), (31198337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31198337
  · decide +kernel

theorem prime_206857487 : Nat.Prime 206857487 := by
  apply nodeValid_prime [2, 11, 197, 4339] ⟨206857487, 5, [(2, 1), (11, 2), (197, 1), (4339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_197
    · exact prime_4339
  · decide +kernel

theorem prime_237532459 : Nat.Prime 237532459 := by
  apply nodeValid_prime [2, 3, 39588743] ⟨237532459, 2, [(2, 1), (3, 1), (39588743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39588743
  · decide +kernel

theorem prime_339843941 : Nat.Prime 339843941 := by
  apply nodeValid_prime [2, 5, 17, 999541] ⟨339843941, 2, [(2, 2), (5, 1), (17, 1), (999541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_999541
  · decide +kernel

theorem prime_343930823 : Nat.Prime 343930823 := by
  apply nodeValid_prime [2, 23, 167, 44771] ⟨343930823, 5, [(2, 1), (23, 1), (167, 1), (44771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_167
    · exact prime_44771
  · decide +kernel

theorem prime_359877341 : Nat.Prime 359877341 := by
  apply nodeValid_prime [2, 5, 17993867] ⟨359877341, 3, [(2, 2), (5, 1), (17993867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17993867
  · decide +kernel

theorem prime_452288987 : Nat.Prime 452288987 := by
  apply nodeValid_prime [2, 1669, 135497] ⟨452288987, 2, [(2, 1), (1669, 1), (135497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1669
    · exact prime_135497
  · decide +kernel

theorem prime_482486929 : Nat.Prime 482486929 := by
  apply nodeValid_prime [2, 3, 7, 11, 17, 1097] ⟨482486929, 31, [(2, 4), (3, 1), (7, 2), (11, 1), (17, 1), (1097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_1097
  · decide +kernel

theorem prime_491068229 : Nat.Prime 491068229 := by
  apply nodeValid_prime [2, 7, 17538151] ⟨491068229, 2, [(2, 2), (7, 1), (17538151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17538151
  · decide +kernel

theorem prime_604660523 : Nat.Prime 604660523 := by
  apply nodeValid_prime [2, 17, 19, 936007] ⟨604660523, 2, [(2, 1), (17, 1), (19, 1), (936007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_936007
  · decide +kernel

theorem prime_733127797 : Nat.Prime 733127797 := by
  apply nodeValid_prime [2, 3, 20364661] ⟨733127797, 2, [(2, 2), (3, 2), (20364661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20364661
  · decide +kernel

theorem prime_794212061 : Nat.Prime 794212061 := by
  apply nodeValid_prime [2, 5, 83, 478441] ⟨794212061, 2, [(2, 2), (5, 1), (83, 1), (478441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
    · exact prime_478441
  · decide +kernel

theorem prime_1142054063 : Nat.Prime 1142054063 := by
  apply nodeValid_prime [2, 37, 15433163] ⟨1142054063, 5, [(2, 1), (37, 1), (15433163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_15433163
  · decide +kernel

theorem prime_1562298737 : Nat.Prime 1562298737 := by
  apply nodeValid_prime [2, 23, 479, 8863] ⟨1562298737, 3, [(2, 4), (23, 1), (479, 1), (8863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_479
    · exact prime_8863
  · decide +kernel

theorem prime_2358726091 : Nat.Prime 2358726091 := by
  apply nodeValid_prime [2, 3, 5, 7, 11232029] ⟨2358726091, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (11232029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11232029
  · decide +kernel

theorem prime_2524367081 : Nat.Prime 2524367081 := by
  apply nodeValid_prime [2, 5, 257, 245561] ⟨2524367081, 3, [(2, 3), (5, 1), (257, 1), (245561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_257
    · exact prime_245561
  · decide +kernel

theorem prime_3866967233 : Nat.Prime 3866967233 := by
  apply nodeValid_prime [2, 593, 101891] ⟨3866967233, 3, [(2, 6), (593, 1), (101891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_593
    · exact prime_101891
  · decide +kernel

theorem prime_5547759953 : Nat.Prime 5547759953 := by
  apply nodeValid_prime [2, 7, 49533571] ⟨5547759953, 3, [(2, 4), (7, 1), (49533571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_49533571
  · decide +kernel

theorem prime_12651189253 : Nat.Prime 12651189253 := by
  apply nodeValid_prime [2, 3, 13, 53, 117703] ⟨12651189253, 2, [(2, 2), (3, 1), (13, 2), (53, 1), (117703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_117703
  · decide +kernel

theorem prime_17386547077 : Nat.Prime 17386547077 := by
  apply nodeValid_prime [2, 3, 269, 598463] ⟨17386547077, 6, [(2, 2), (3, 3), (269, 1), (598463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_598463
  · decide +kernel

theorem prime_28790187281 : Nat.Prime 28790187281 := by
  apply nodeValid_prime [2, 5, 359877341] ⟨28790187281, 3, [(2, 4), (5, 1), (359877341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_359877341
  · decide +kernel

theorem prime_57580374563 : Nat.Prime 57580374563 := by
  apply nodeValid_prime [2, 28790187281] ⟨57580374563, 2, [(2, 1), (28790187281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28790187281
  · decide +kernel

theorem prime_93448039339 : Nat.Prime 93448039339 := by
  apply nodeValid_prime [2, 3, 283, 1321, 1543] ⟨93448039339, 2, [(2, 1), (3, 4), (283, 1), (1321, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_1321
    · exact prime_1543
  · decide +kernel

theorem prime_93834693289 : Nat.Prime 93834693289 := by
  apply nodeValid_prime [2, 3, 7, 10181, 18287] ⟨93834693289, 11, [(2, 3), (3, 2), (7, 1), (10181, 1), (18287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_10181
    · exact prime_18287
  · decide +kernel

theorem prime_115160749127 : Nat.Prime 115160749127 := by
  apply nodeValid_prime [2, 57580374563] ⟨115160749127, 5, [(2, 1), (57580374563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_57580374563
  · decide +kernel

theorem prime_170085656701 : Nat.Prime 170085656701 := by
  apply nodeValid_prime [2, 3, 5, 587, 321949] ⟨170085656701, 2, [(2, 2), (3, 2), (5, 2), (587, 1), (321949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_587
    · exact prime_321949
  · decide +kernel

theorem prime_255921774371 : Nat.Prime 255921774371 := by
  apply nodeValid_prime [2, 5, 89293, 286609] ⟨255921774371, 7, [(2, 1), (5, 1), (89293, 1), (286609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89293
    · exact prime_286609
  · decide +kernel

theorem prime_345482243987 : Nat.Prime 345482243987 := by
  apply nodeValid_prime [2, 11, 59, 3467, 76771] ⟨345482243987, 2, [(2, 1), (11, 1), (59, 1), (3467, 1), (76771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_3467
    · exact prime_76771
  · decide +kernel

theorem prime_508146674983 : Nat.Prime 508146674983 := by
  apply nodeValid_prime [2, 3, 457, 185319721] ⟨508146674983, 5, [(2, 1), (3, 1), (457, 1), (185319721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_457
    · exact prime_185319721
  · decide +kernel

theorem prime_1031117210429 : Nat.Prime 1031117210429 := by
  apply nodeValid_prime [2, 110939, 2323613] ⟨1031117210429, 2, [(2, 2), (110939, 1), (2323613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_110939
    · exact prime_2323613
  · decide +kernel

theorem prime_1034312691641 : Nat.Prime 1034312691641 := by
  apply nodeValid_prime [2, 5, 1361, 18999131] ⟨1034312691641, 3, [(2, 3), (5, 1), (1361, 1), (18999131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1361
    · exact prime_18999131
  · decide +kernel

theorem prime_1039653387743 : Nat.Prime 1039653387743 := by
  apply nodeValid_prime [2, 2777, 187190023] ⟨1039653387743, 5, [(2, 1), (2777, 1), (187190023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2777
    · exact prime_187190023
  · decide +kernel

theorem prime_2028375049517 : Nat.Prime 2028375049517 := by
  apply nodeValid_prime [2, 1051, 482486929] ⟨2028375049517, 2, [(2, 2), (1051, 1), (482486929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1051
    · exact prime_482486929
  · decide +kernel

theorem prime_2028375049607 : Nat.Prime 2028375049607 := by
  apply nodeValid_prime [2, 416401, 2435603] ⟨2028375049607, 5, [(2, 1), (416401, 1), (2435603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_416401
    · exact prime_2435603
  · decide +kernel

theorem prime_2028375050311 : Nat.Prime 2028375050311 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 131, 12149] ⟨2028375050311, 6, [(2, 1), (3, 2), (5, 1), (7, 2), (17, 2), (131, 1), (12149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_131
    · exact prime_12149
  · decide +kernel

theorem prime_2030480142799 : Nat.Prime 2030480142799 := by
  apply nodeValid_prime [2, 3, 61, 5547759953] ⟨2030480142799, 3, [(2, 1), (3, 1), (61, 1), (5547759953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_5547759953
  · decide +kernel

theorem prime_2030480160311 : Nat.Prime 2030480160311 := by
  apply nodeValid_prime [2, 5, 7, 17, 31, 55041479] ⟨2030480160311, 7, [(2, 1), (5, 1), (7, 1), (17, 1), (31, 1), (55041479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_55041479
  · decide +kernel

theorem prime_2030480164547 : Nat.Prime 2030480164547 := by
  apply nodeValid_prime [2, 36899, 27514027] ⟨2030480164547, 2, [(2, 1), (36899, 1), (27514027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_36899
    · exact prime_27514027
  · decide +kernel

theorem prime_2032586699933 : Nat.Prime 2032586699933 := by
  apply nodeValid_prime [2, 508146674983] ⟨2032586699933, 2, [(2, 2), (508146674983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_508146674983
  · decide +kernel

theorem prime_2032586700553 : Nat.Prime 2032586700553 := by
  apply nodeValid_prime [2, 3, 24251, 1164091] ⟨2032586700553, 5, [(2, 3), (3, 2), (24251, 1), (1164091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24251
    · exact prime_1164091
  · decide +kernel

theorem prime_2032586707579 : Nat.Prime 2032586707579 := by
  apply nodeValid_prime [2, 3, 7, 107, 452288987] ⟨2032586707579, 7, [(2, 1), (3, 1), (7, 1), (107, 1), (452288987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_452288987
  · decide +kernel

theorem prime_2034694744889 : Nat.Prime 2034694744889 := by
  apply nodeValid_prime [2, 13, 6199, 3156053] ⟨2034694744889, 3, [(2, 3), (13, 1), (6199, 1), (3156053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_6199
    · exact prime_3156053
  · decide +kernel

theorem prime_2034694745189 : Nat.Prime 2034694745189 := by
  apply nodeValid_prime [2, 7, 73, 139, 7161493] ⟨2034694745189, 2, [(2, 2), (7, 1), (73, 1), (139, 1), (7161493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_139
    · exact prime_7161493
  · decide +kernel

theorem prime_2034694748869 : Nat.Prime 2034694748869 := by
  apply nodeValid_prime [2, 3, 17, 29, 343930823] ⟨2034694748869, 2, [(2, 2), (3, 1), (17, 1), (29, 1), (343930823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_29
    · exact prime_343930823
  · decide +kernel

theorem prime_2036804275549 : Nat.Prime 2036804275549 := by
  apply nodeValid_prime [2, 3, 7, 37, 1033, 211469] ⟨2036804275549, 2, [(2, 2), (3, 2), (7, 1), (37, 1), (1033, 1), (211469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_1033
    · exact prime_211469
  · decide +kernel

theorem prime_2036804298049 : Nat.Prime 2036804298049 := by
  apply nodeValid_prime [2, 3, 13, 4253, 21319] ⟨2036804298049, 7, [(2, 6), (3, 3), (13, 1), (4253, 1), (21319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4253
    · exact prime_21319
  · decide +kernel

theorem prime_2036804298961 : Nat.Prime 2036804298961 := by
  apply nodeValid_prime [2, 3, 5, 47, 6301, 28657] ⟨2036804298961, 14, [(2, 4), (3, 1), (5, 1), (47, 1), (6301, 1), (28657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_6301
    · exact prime_28657
  · decide +kernel

theorem prime_2038915281679 : Nat.Prime 2038915281679 := by
  apply nodeValid_prime [2, 3, 11, 229, 2963, 4139] ⟨2038915281679, 6, [(2, 1), (3, 1), (11, 2), (229, 1), (2963, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_229
    · exact prime_2963
    · exact prime_4139
  · decide +kernel

theorem prime_2038915283557 : Nat.Prime 2038915283557 := by
  apply nodeValid_prime [2, 3, 281, 604660523] ⟨2038915283557, 2, [(2, 2), (3, 1), (281, 1), (604660523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_604660523
  · decide +kernel

theorem prime_2038915286809 : Nat.Prime 2038915286809 := by
  apply nodeValid_prime [2, 3, 173, 491068229] ⟨2038915286809, 17, [(2, 3), (3, 1), (173, 1), (491068229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_491068229
  · decide +kernel

theorem prime_2041027786849 : Nat.Prime 2041027786849 := by
  apply nodeValid_prime [2, 3, 29, 733127797] ⟨2041027786849, 11, [(2, 5), (3, 1), (29, 1), (733127797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_733127797
  · decide +kernel

theorem prime_2041027880273 : Nat.Prime 2041027880273 := by
  apply nodeValid_prime [2, 149269, 854593] ⟨2041027880273, 3, [(2, 4), (149269, 1), (854593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149269
    · exact prime_854593
  · decide +kernel

theorem prime_2041027880413 : Nat.Prime 2041027880413 := by
  apply nodeValid_prime [2, 3, 170085656701] ⟨2041027880413, 2, [(2, 2), (3, 1), (170085656701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_170085656701
  · decide +kernel

theorem prime_2043141773293 : Nat.Prime 2043141773293 := by
  apply nodeValid_prime [2, 3, 167, 339843941] ⟨2043141773293, 2, [(2, 2), (3, 2), (167, 1), (339843941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_339843941
  · decide +kernel

theorem prime_2043141857621 : Nat.Prime 2043141857621 := by
  apply nodeValid_prime [2, 5, 19, 15787, 340577] ⟨2043141857621, 3, [(2, 2), (5, 1), (19, 1), (15787, 1), (340577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_15787
    · exact prime_340577
  · decide +kernel

theorem prime_2043141858749 : Nat.Prime 2043141858749 := by
  apply nodeValid_prime [2, 347, 3767, 390763] ⟨2043141858749, 2, [(2, 2), (347, 1), (3767, 1), (390763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_3767
    · exact prime_390763
  · decide +kernel

theorem prime_2045257220833 : Nat.Prime 2045257220833 := by
  apply nodeValid_prime [2, 3, 7, 8741, 348191] ⟨2045257220833, 10, [(2, 5), (3, 1), (7, 1), (8741, 1), (348191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8741
    · exact prime_348191
  · decide +kernel

theorem prime_2045257221149 : Nat.Prime 2045257221149 := by
  apply nodeValid_prime [2, 173, 2683, 1101593] ⟨2045257221149, 2, [(2, 2), (173, 1), (2683, 1), (1101593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_2683
    · exact prime_1101593
  · decide +kernel

theorem prime_2045257243481 : Nat.Prime 2045257243481 := by
  apply nodeValid_prime [2, 5, 11, 179, 25968223] ⟨2045257243481, 6, [(2, 3), (5, 1), (11, 1), (179, 1), (25968223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_179
    · exact prime_25968223
  · decide +kernel

theorem prime_2047374194969 : Nat.Prime 2047374194969 := by
  apply nodeValid_prime [2, 255921774371] ⟨2047374194969, 3, [(2, 3), (255921774371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_255921774371
  · decide +kernel

theorem prime_2047374246059 : Nat.Prime 2047374246059 := by
  apply nodeValid_prime [2, 31, 9283, 3557273] ⟨2047374246059, 2, [(2, 1), (31, 1), (9283, 1), (3557273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_9283
    · exact prime_3557273
  · decide +kernel

theorem prime_2047374246989 : Nat.Prime 2047374246989 := by
  apply nodeValid_prime [2, 7, 31, 2358726091] ⟨2047374246989, 2, [(2, 2), (7, 1), (31, 1), (2358726091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_2358726091
  · decide +kernel

theorem prime_2049492633491 : Nat.Prime 2049492633491 := by
  apply nodeValid_prime [2, 5, 53, 3866967233] ⟨2049492633491, 2, [(2, 1), (5, 1), (53, 1), (3866967233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53
    · exact prime_3866967233
  · decide +kernel

theorem prime_2049492658987 : Nat.Prime 2049492658987 := by
  apply nodeValid_prime [2, 3, 12651189253] ⟨2049492658987, 3, [(2, 1), (3, 4), (12651189253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12651189253
  · decide +kernel

theorem prime_2049492658991 : Nat.Prime 2049492658991 := by
  apply nodeValid_prime [2, 5, 7, 283, 3079, 33601] ⟨2049492658991, 7, [(2, 1), (5, 1), (7, 1), (283, 1), (3079, 1), (33601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_283
    · exact prime_3079
    · exact prime_33601
  · decide +kernel

theorem prime_2051612555087 : Nat.Prime 2051612555087 := by
  apply nodeValid_prime [2, 59, 17386547077] ⟨2051612555087, 5, [(2, 1), (59, 1), (17386547077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_17386547077
  · decide +kernel

theorem prime_2051612556067 : Nat.Prime 2051612556067 := by
  apply nodeValid_prime [2, 3, 19, 29, 206857487] ⟨2051612556067, 2, [(2, 1), (3, 2), (19, 1), (29, 1), (206857487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_206857487
  · decide +kernel

theorem prime_2053733964133 : Nat.Prime 2053733964133 := by
  apply nodeValid_prime [2, 3, 39301, 4354711] ⟨2053733964133, 2, [(2, 2), (3, 1), (39301, 1), (4354711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39301
    · exact prime_4354711
  · decide +kernel

theorem prime_2053733984629 : Nat.Prime 2053733984629 := by
  apply nodeValid_prime [2, 3, 32533, 5260643] ⟨2053733984629, 6, [(2, 2), (3, 1), (32533, 1), (5260643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32533
    · exact prime_5260643
  · decide +kernel

theorem prime_2055856853693 : Nat.Prime 2055856853693 := by
  apply nodeValid_prime [2, 61, 113, 271, 503, 547] ⟨2055856853693, 2, [(2, 2), (61, 1), (113, 1), (271, 1), (503, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_113
    · exact prime_271
    · exact prime_503
    · exact prime_547
  · decide +kernel

theorem prime_2055856865459 : Nat.Prime 2055856865459 := by
  apply nodeValid_prime [2, 11, 93448039339] ⟨2055856865459, 2, [(2, 1), (11, 1), (93448039339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_93448039339
  · decide +kernel

theorem prime_2055856865597 : Nat.Prime 2055856865597 := by
  apply nodeValid_prime [2, 12109, 42444811] ⟨2055856865597, 2, [(2, 2), (12109, 1), (42444811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_12109
    · exact prime_42444811
  · decide +kernel

theorem prime_2057981224777 : Nat.Prime 2057981224777 := by
  apply nodeValid_prime [2, 3, 19, 237532459] ⟨2057981224777, 10, [(2, 3), (3, 1), (19, 2), (237532459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_237532459
  · decide +kernel

theorem prime_2057981421527 : Nat.Prime 2057981421527 := by
  apply nodeValid_prime [2, 17, 53, 1142054063] ⟨2057981421527, 5, [(2, 1), (17, 1), (53, 1), (1142054063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_53
    · exact prime_1142054063
  · decide +kernel

theorem prime_2057981422187 : Nat.Prime 2057981422187 := by
  apply nodeValid_prime [2, 19, 59, 181, 389, 13037] ⟨2057981422187, 2, [(2, 1), (19, 1), (59, 1), (181, 1), (389, 1), (13037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59
    · exact prime_181
    · exact prime_389
    · exact prime_13037
  · decide +kernel

theorem prime_2060107054237 : Nat.Prime 2060107054237 := by
  apply nodeValid_prime [2, 3, 7, 11, 29, 79, 108131] ⟨2060107054237, 5, [(2, 2), (3, 3), (7, 1), (11, 1), (29, 1), (79, 1), (108131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_79
    · exact prime_108131
  · decide +kernel

theorem prime_2060107054417 : Nat.Prime 2060107054417 := by
  apply nodeValid_prime [2, 3, 34729, 411941] ⟨2060107054417, 5, [(2, 4), (3, 2), (34729, 1), (411941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34729
    · exact prime_411941
  · decide +kernel

theorem prime_2060107080851 : Nat.Prime 2060107080851 := by
  apply nodeValid_prime [2, 5, 7, 13, 47, 1376203] ⟨2060107080851, 17, [(2, 1), (5, 2), (7, 2), (13, 1), (47, 1), (1376203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_47
    · exact prime_1376203
  · decide +kernel

theorem prime_2062234332217 : Nat.Prime 2062234332217 := by
  apply nodeValid_prime [2, 3, 19, 31, 127, 463, 827] ⟨2062234332217, 14, [(2, 3), (3, 2), (19, 1), (31, 1), (127, 1), (463, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_31
    · exact prime_127
    · exact prime_463
    · exact prime_827
  · decide +kernel

theorem prime_2062234332841 : Nat.Prime 2062234332841 := by
  apply nodeValid_prime [2, 3, 5, 11, 1562298737] ⟨2062234332841, 23, [(2, 3), (3, 1), (5, 1), (11, 1), (1562298737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1562298737
  · decide +kernel

theorem prime_2062234420859 : Nat.Prime 2062234420859 := by
  apply nodeValid_prime [2, 1031117210429] ⟨2062234420859, 2, [(2, 1), (1031117210429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1031117210429
  · decide +kernel

theorem prime_2064363242329 : Nat.Prime 2064363242329 := by
  apply nodeValid_prime [2, 3, 37, 43, 103, 58321] ⟨2064363242329, 13, [(2, 3), (3, 3), (37, 1), (43, 1), (103, 1), (58321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_43
    · exact prime_103
    · exact prime_58321
  · decide +kernel

theorem prime_2064363242941 : Nat.Prime 2064363242941 := by
  apply nodeValid_prime [2, 3, 5, 107, 1117, 95957] ⟨2064363242941, 2, [(2, 2), (3, 2), (5, 1), (107, 1), (1117, 1), (95957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
    · exact prime_1117
    · exact prime_95957
  · decide +kernel

theorem prime_2064363252359 : Nat.Prime 2064363252359 := by
  apply nodeValid_prime [2, 11, 93834693289] ⟨2064363252359, 7, [(2, 1), (11, 1), (93834693289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_93834693289
  · decide +kernel

theorem prime_2066493451619 : Nat.Prime 2066493451619 := by
  apply nodeValid_prime [2, 216379, 4775171] ⟨2066493451619, 2, [(2, 1), (216379, 1), (4775171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_216379
    · exact prime_4775171
  · decide +kernel

theorem prime_2066493451709 : Nat.Prime 2066493451709 := by
  apply nodeValid_prime [2, 7, 211, 1297, 269683] ⟨2066493451709, 2, [(2, 2), (7, 1), (211, 1), (1297, 1), (269683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
    · exact prime_1297
    · exact prime_269683
  · decide +kernel

theorem prime_2066493574573 : Nat.Prime 2066493574573 := by
  apply nodeValid_prime [2, 3, 7, 173, 142202971] ⟨2066493574573, 5, [(2, 2), (3, 1), (7, 1), (173, 1), (142202971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_173
    · exact prime_142202971
  · decide +kernel

theorem prime_2068625336171 : Nat.Prime 2068625336171 := by
  apply nodeValid_prime [2, 5, 1553, 6997, 19037] ⟨2068625336171, 2, [(2, 1), (5, 1), (1553, 1), (6997, 1), (19037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1553
    · exact prime_6997
    · exact prime_19037
  · decide +kernel

theorem prime_2068625337377 : Nat.Prime 2068625337377 := by
  apply nodeValid_prime [2, 13, 311, 15989251] ⟨2068625337377, 3, [(2, 5), (13, 1), (311, 1), (15989251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_311
    · exact prime_15989251
  · decide +kernel

theorem prime_2068625383283 : Nat.Prime 2068625383283 := by
  apply nodeValid_prime [2, 1034312691641] ⟨2068625383283, 2, [(2, 1), (1034312691641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1034312691641
  · decide +kernel

theorem prime_2070758674547 : Nat.Prime 2070758674547 := by
  apply nodeValid_prime [2, 53731, 19269683] ⟨2070758674547, 2, [(2, 1), (53731, 1), (19269683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53731
    · exact prime_19269683
  · decide +kernel

theorem prime_2070758681137 : Nat.Prime 2070758681137 := by
  apply nodeValid_prime [2, 3, 41, 53, 401, 5501] ⟨2070758681137, 5, [(2, 4), (3, 3), (41, 1), (53, 1), (401, 1), (5501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_53
    · exact prime_401
    · exact prime_5501
  · decide +kernel

theorem prime_2070758681617 : Nat.Prime 2070758681617 := by
  apply nodeValid_prime [2, 3, 269, 3229, 49667] ⟨2070758681617, 5, [(2, 4), (3, 1), (269, 1), (3229, 1), (49667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_3229
    · exact prime_49667
  · decide +kernel

theorem prime_2072893463923 : Nat.Prime 2072893463923 := by
  apply nodeValid_prime [2, 3, 345482243987] ⟨2072893463923, 3, [(2, 1), (3, 1), (345482243987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_345482243987
  · decide +kernel

theorem prime_2072893479211 : Nat.Prime 2072893479211 := by
  apply nodeValid_prime [2, 3, 5, 29, 794212061] ⟨2072893479211, 2, [(2, 1), (3, 2), (5, 1), (29, 1), (794212061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_794212061
  · decide +kernel

theorem prime_2072893484287 : Nat.Prime 2072893484287 := by
  apply nodeValid_prime [2, 3, 115160749127] ⟨2072893484287, 3, [(2, 1), (3, 2), (115160749127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115160749127
  · decide +kernel

theorem prime_2075029740583 : Nat.Prime 2075029740583 := by
  apply nodeValid_prime [2, 3, 137, 2524367081] ⟨2075029740583, 5, [(2, 1), (3, 1), (137, 1), (2524367081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_2524367081
  · decide +kernel

theorem prime_2075029740661 : Nat.Prime 2075029740661 := by
  apply nodeValid_prime [2, 3, 5, 17, 353, 5763011] ⟨2075029740661, 6, [(2, 2), (3, 1), (5, 1), (17, 1), (353, 1), (5763011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_353
    · exact prime_5763011
  · decide +kernel

theorem prime_2075029740941 : Nat.Prime 2075029740941 := by
  apply nodeValid_prime [2, 5, 13, 1123, 7106753] ⟨2075029740941, 2, [(2, 2), (5, 1), (13, 1), (1123, 1), (7106753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_1123
    · exact prime_7106753
  · decide +kernel

theorem prime_2077167514021 : Nat.Prime 2077167514021 := by
  apply nodeValid_prime [2, 3, 5, 139, 677, 367889] ⟨2077167514021, 2, [(2, 2), (3, 1), (5, 1), (139, 1), (677, 1), (367889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_139
    · exact prime_677
    · exact prime_367889
  · decide +kernel

theorem prime_2077167781141 : Nat.Prime 2077167781141 := by
  apply nodeValid_prime [2, 3, 5, 19, 127, 173, 653] ⟨2077167781141, 6, [(2, 2), (3, 1), (5, 1), (19, 1), (127, 2), (173, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_127
    · exact prime_173
    · exact prime_653
  · decide +kernel

theorem prime_2077167781867 : Nat.Prime 2077167781867 := by
  apply nodeValid_prime [2, 3, 41, 2999, 2815529] ⟨2077167781867, 2, [(2, 1), (3, 1), (41, 1), (2999, 1), (2815529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2999
    · exact prime_2815529
  · decide +kernel

theorem prime_2079306698891 : Nat.Prime 2079306698891 := by
  apply nodeValid_prime [2, 5, 4127, 50383007] ⟨2079306698891, 2, [(2, 1), (5, 1), (4127, 1), (50383007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4127
    · exact prime_50383007
  · decide +kernel

theorem prime_2079306698929 : Nat.Prime 2079306698929 := by
  apply nodeValid_prime [2, 3, 6379, 6790859] ⟨2079306698929, 7, [(2, 4), (3, 1), (6379, 1), (6790859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6379
    · exact prime_6790859
  · decide +kernel

theorem prime_2079306775487 : Nat.Prime 2079306775487 := by
  apply nodeValid_prime [2, 1039653387743] ⟨2079306775487, 5, [(2, 1), (1039653387743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1039653387743
  · decide +kernel

end Sude.Lucas.Generated
