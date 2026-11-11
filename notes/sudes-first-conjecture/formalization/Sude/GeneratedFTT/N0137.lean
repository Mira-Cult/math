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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0105
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0123
import Sude.GeneratedFTT.N0131

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_12893 : Nat.Prime 12893 := by
  apply nodeValid_prime [2, 11, 293] ⟨12893, 3, [(2, 2), (11, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_293
  · decide +kernel

theorem prime_17293 : Nat.Prime 17293 := by
  apply nodeValid_prime [2, 3, 11, 131] ⟨17293, 7, [(2, 2), (3, 1), (11, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
  · decide +kernel

theorem prime_24113 : Nat.Prime 24113 := by
  apply nodeValid_prime [2, 11, 137] ⟨24113, 3, [(2, 4), (11, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_137
  · decide +kernel

theorem prime_28537 : Nat.Prime 28537 := by
  apply nodeValid_prime [2, 3, 29, 41] ⟨28537, 5, [(2, 3), (3, 1), (29, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_41
  · decide +kernel

theorem prime_34757 : Nat.Prime 34757 := by
  apply nodeValid_prime [2, 8689] ⟨34757, 2, [(2, 2), (8689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8689
  · decide +kernel

theorem prime_35963 : Nat.Prime 35963 := by
  apply nodeValid_prime [2, 17981] ⟨35963, 2, [(2, 1), (17981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17981
  · decide +kernel

theorem prime_58111 : Nat.Prime 58111 := by
  apply nodeValid_prime [2, 3, 5, 13, 149] ⟨58111, 12, [(2, 1), (3, 1), (5, 1), (13, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_149
  · decide +kernel

theorem prime_58369 : Nat.Prime 58369 := by
  apply nodeValid_prime [2, 3, 19] ⟨58369, 7, [(2, 10), (3, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_61909 : Nat.Prime 61909 := by
  apply nodeValid_prime [2, 3, 7, 11, 67] ⟨61909, 6, [(2, 2), (3, 1), (7, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_62207 : Nat.Prime 62207 := by
  apply nodeValid_prime [2, 19, 1637] ⟨62207, 5, [(2, 1), (19, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1637
  · decide +kernel

theorem prime_71167 : Nat.Prime 71167 := by
  apply nodeValid_prime [2, 3, 29, 409] ⟨71167, 3, [(2, 1), (3, 1), (29, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_409
  · decide +kernel

theorem prime_71941 : Nat.Prime 71941 := by
  apply nodeValid_prime [2, 3, 5, 11, 109] ⟨71941, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_109
  · decide +kernel

theorem prime_73013 : Nat.Prime 73013 := by
  apply nodeValid_prime [2, 18253] ⟨73013, 2, [(2, 2), (18253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18253
  · decide +kernel

theorem prime_77359 : Nat.Prime 77359 := by
  apply nodeValid_prime [2, 3, 12893] ⟨77359, 3, [(2, 1), (3, 1), (12893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12893
  · decide +kernel

theorem prime_88337 : Nat.Prime 88337 := by
  apply nodeValid_prime [2, 5521] ⟨88337, 3, [(2, 4), (5521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5521
  · decide +kernel

theorem prime_91393 : Nat.Prime 91393 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨91393, 23, [(2, 8), (3, 1), (7, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_93889 : Nat.Prime 93889 := by
  apply nodeValid_prime [2, 3, 163] ⟨93889, 14, [(2, 6), (3, 2), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
  · decide +kernel

theorem prime_110339 : Nat.Prime 110339 := by
  apply nodeValid_prime [2, 43, 1283] ⟨110339, 2, [(2, 1), (43, 1), (1283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1283
  · decide +kernel

theorem prime_114161 : Nat.Prime 114161 := by
  apply nodeValid_prime [2, 5, 1427] ⟨114161, 3, [(2, 4), (5, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1427
  · decide +kernel

theorem prime_119551 : Nat.Prime 119551 := by
  apply nodeValid_prime [2, 3, 5, 797] ⟨119551, 3, [(2, 1), (3, 1), (5, 2), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_797
  · decide +kernel

theorem prime_137941 : Nat.Prime 137941 := by
  apply nodeValid_prime [2, 3, 5, 11, 19] ⟨137941, 2, [(2, 2), (3, 1), (5, 1), (11, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_145799 : Nat.Prime 145799 := by
  apply nodeValid_prime [2, 269, 271] ⟨145799, 11, [(2, 1), (269, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_269
    · exact prime_271
  · decide +kernel

theorem prime_149297 : Nat.Prime 149297 := by
  apply nodeValid_prime [2, 7, 31, 43] ⟨149297, 3, [(2, 4), (7, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_161017 : Nat.Prime 161017 := by
  apply nodeValid_prime [2, 3, 6709] ⟨161017, 7, [(2, 3), (3, 1), (6709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6709
  · decide +kernel

theorem prime_233477 : Nat.Prime 233477 := by
  apply nodeValid_prime [2, 58369] ⟨233477, 2, [(2, 2), (58369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_58369
  · decide +kernel

theorem prime_246811 : Nat.Prime 246811 := by
  apply nodeValid_prime [2, 3, 5, 19, 433] ⟨246811, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_433
  · decide +kernel

theorem prime_299027 : Nat.Prime 299027 := by
  apply nodeValid_prime [2, 7, 13, 31, 53] ⟨299027, 5, [(2, 1), (7, 1), (13, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_338269 : Nat.Prime 338269 := by
  apply nodeValid_prime [2, 3, 7, 4027] ⟨338269, 10, [(2, 2), (3, 1), (7, 1), (4027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4027
  · decide +kernel

theorem prime_371927 : Nat.Prime 371927 := by
  apply nodeValid_prime [2, 17, 10939] ⟨371927, 5, [(2, 1), (17, 1), (10939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_10939
  · decide +kernel

theorem prime_376153 : Nat.Prime 376153 := by
  apply nodeValid_prime [2, 3, 7, 2239] ⟨376153, 5, [(2, 3), (3, 1), (7, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2239
  · decide +kernel

theorem prime_391283 : Nat.Prime 391283 := by
  apply nodeValid_prime [2, 31, 6311] ⟨391283, 2, [(2, 1), (31, 1), (6311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_6311
  · decide +kernel

theorem prime_396199 : Nat.Prime 396199 := by
  apply nodeValid_prime [2, 3, 11, 23, 29] ⟨396199, 3, [(2, 1), (3, 3), (11, 1), (23, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_29
  · decide +kernel

theorem prime_429563 : Nat.Prime 429563 := by
  apply nodeValid_prime [2, 7, 61, 503] ⟨429563, 2, [(2, 1), (7, 1), (61, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_503
  · decide +kernel

theorem prime_465551 : Nat.Prime 465551 := by
  apply nodeValid_prime [2, 5, 9311] ⟨465551, 7, [(2, 1), (5, 2), (9311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9311
  · decide +kernel

theorem prime_538331 : Nat.Prime 538331 := by
  apply nodeValid_prime [2, 5, 13, 41, 101] ⟨538331, 2, [(2, 1), (5, 1), (13, 1), (41, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
    · exact prime_101
  · decide +kernel

theorem prime_616673 : Nat.Prime 616673 := by
  apply nodeValid_prime [2, 7, 2753] ⟨616673, 3, [(2, 5), (7, 1), (2753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2753
  · decide +kernel

theorem prime_715811 : Nat.Prime 715811 := by
  apply nodeValid_prime [2, 5, 47, 1523] ⟨715811, 2, [(2, 1), (5, 1), (47, 1), (1523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_1523
  · decide +kernel

theorem prime_814789 : Nat.Prime 814789 := by
  apply nodeValid_prime [2, 3, 13, 1741] ⟨814789, 2, [(2, 2), (3, 2), (13, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1741
  · decide +kernel

theorem prime_1081279 : Nat.Prime 1081279 := by
  apply nodeValid_prime [2, 3, 11, 43, 127] ⟨1081279, 6, [(2, 1), (3, 2), (11, 1), (43, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_127
  · decide +kernel

theorem prime_1243133 : Nat.Prime 1243133 := by
  apply nodeValid_prime [2, 11, 19, 1487] ⟨1243133, 2, [(2, 2), (11, 1), (19, 1), (1487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1487
  · decide +kernel

theorem prime_1254257 : Nat.Prime 1254257 := by
  apply nodeValid_prime [2, 277, 283] ⟨1254257, 3, [(2, 4), (277, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_277
    · exact prime_283
  · decide +kernel

theorem prime_1336481 : Nat.Prime 1336481 := by
  apply nodeValid_prime [2, 5, 8353] ⟨1336481, 3, [(2, 5), (5, 1), (8353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8353
  · decide +kernel

theorem prime_1361999 : Nat.Prime 1361999 := by
  apply nodeValid_prime [2, 11, 61909] ⟨1361999, 7, [(2, 1), (11, 1), (61909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61909
  · decide +kernel

theorem prime_1584797 : Nat.Prime 1584797 := by
  apply nodeValid_prime [2, 396199] ⟨1584797, 2, [(2, 2), (396199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_396199
  · decide +kernel

theorem prime_1748167 : Nat.Prime 1748167 := by
  apply nodeValid_prime [2, 3, 7, 107, 389] ⟨1748167, 6, [(2, 1), (3, 1), (7, 1), (107, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
    · exact prime_389
  · decide +kernel

theorem prime_1962397 : Nat.Prime 1962397 := by
  apply nodeValid_prime [2, 3, 19, 151] ⟨1962397, 2, [(2, 2), (3, 2), (19, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_151
  · decide +kernel

theorem prime_2000573 : Nat.Prime 2000573 := by
  apply nodeValid_prime [2, 7, 59, 173] ⟨2000573, 3, [(2, 2), (7, 2), (59, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_173
  · decide +kernel

theorem prime_2090159 : Nat.Prime 2090159 := by
  apply nodeValid_prime [2, 7, 149297] ⟨2090159, 7, [(2, 1), (7, 1), (149297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_149297
  · decide +kernel

theorem prime_2338351 : Nat.Prime 2338351 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 131] ⟨2338351, 3, [(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_131
  · decide +kernel

theorem prime_2630207 : Nat.Prime 2630207 := by
  apply nodeValid_prime [2, 17, 77359] ⟨2630207, 5, [(2, 1), (17, 1), (77359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_77359
  · decide +kernel

theorem prime_3192227 : Nat.Prime 3192227 := by
  apply nodeValid_prime [2, 17, 93889] ⟨3192227, 2, [(2, 1), (17, 1), (93889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_93889
  · decide +kernel

theorem prime_3229987 : Nat.Prime 3229987 := by
  apply nodeValid_prime [2, 3, 538331] ⟨3229987, 2, [(2, 1), (3, 1), (538331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_538331
  · decide +kernel

theorem prime_4773173 : Nat.Prime 4773173 := by
  apply nodeValid_prime [2, 43, 27751] ⟨4773173, 2, [(2, 2), (43, 1), (27751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_27751
  · decide +kernel

theorem prime_4879993 : Nat.Prime 4879993 := by
  apply nodeValid_prime [2, 3, 13, 15641] ⟨4879993, 7, [(2, 3), (3, 1), (13, 1), (15641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_15641
  · decide +kernel

theorem prime_5212841 : Nat.Prime 5212841 := by
  apply nodeValid_prime [2, 5, 19] ⟨5212841, 3, [(2, 3), (5, 1), (19, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_6452801 : Nat.Prime 6452801 := by
  apply nodeValid_prime [2, 5, 37, 109] ⟨6452801, 3, [(2, 6), (5, 2), (37, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_109
  · decide +kernel

theorem prime_6728521 : Nat.Prime 6728521 := by
  apply nodeValid_prime [2, 3, 5, 47, 1193] ⟨6728521, 22, [(2, 3), (3, 1), (5, 1), (47, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_1193
  · decide +kernel

theorem prime_8119337 : Nat.Prime 8119337 := by
  apply nodeValid_prime [2, 17, 227, 263] ⟨8119337, 3, [(2, 3), (17, 1), (227, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_227
    · exact prime_263
  · decide +kernel

theorem prime_8147891 : Nat.Prime 8147891 := by
  apply nodeValid_prime [2, 5, 814789] ⟨8147891, 2, [(2, 1), (5, 1), (814789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_814789
  · decide +kernel

theorem prime_8589733 : Nat.Prime 8589733 := by
  apply nodeValid_prime [2, 3, 715811] ⟨8589733, 2, [(2, 2), (3, 1), (715811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_715811
  · decide +kernel

theorem prime_8945207 : Nat.Prime 8945207 := by
  apply nodeValid_prime [2, 23, 139, 1399] ⟨8945207, 5, [(2, 1), (23, 1), (139, 1), (1399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_139
    · exact prime_1399
  · decide +kernel

theorem prime_9546347 : Nat.Prime 9546347 := by
  apply nodeValid_prime [2, 4773173] ⟨9546347, 2, [(2, 1), (4773173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4773173
  · decide +kernel

theorem prime_10839467 : Nat.Prime 10839467 := by
  apply nodeValid_prime [2, 11, 283, 1741] ⟨10839467, 2, [(2, 1), (11, 1), (283, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_283
    · exact prime_1741
  · decide +kernel

theorem prime_12905603 : Nat.Prime 12905603 := by
  apply nodeValid_prime [2, 6452801] ⟨12905603, 2, [(2, 1), (6452801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6452801
  · decide +kernel

theorem prime_18149819 : Nat.Prime 18149819 := by
  apply nodeValid_prime [2, 31, 61, 4799] ⟨18149819, 2, [(2, 1), (31, 1), (61, 1), (4799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_61
    · exact prime_4799
  · decide +kernel

theorem prime_18445919 : Nat.Prime 18445919 := by
  apply nodeValid_prime [2, 17, 257, 2111] ⟨18445919, 7, [(2, 1), (17, 1), (257, 1), (2111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_257
    · exact prime_2111
  · decide +kernel

theorem prime_19811501 : Nat.Prime 19811501 := by
  apply nodeValid_prime [2, 5, 39623] ⟨19811501, 2, [(2, 2), (5, 3), (39623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_39623
  · decide +kernel

theorem prime_28430557 : Nat.Prime 28430557 := by
  apply nodeValid_prime [2, 3, 7, 11, 29, 1061] ⟨28430557, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (29, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_29
    · exact prime_1061
  · decide +kernel

theorem prime_35221871 : Nat.Prime 35221871 := by
  apply nodeValid_prime [2, 5, 41, 271, 317] ⟨35221871, 11, [(2, 1), (5, 1), (41, 1), (271, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_271
    · exact prime_317
  · decide +kernel

theorem prime_35530673 : Nat.Prime 35530673 := by
  apply nodeValid_prime [2, 71, 31277] ⟨35530673, 3, [(2, 4), (71, 1), (31277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_31277
  · decide +kernel

theorem prime_46695401 : Nat.Prime 46695401 := by
  apply nodeValid_prime [2, 5, 233477] ⟨46695401, 3, [(2, 3), (5, 2), (233477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_233477
  · decide +kernel

theorem prime_56500007 : Nat.Prime 56500007 := by
  apply nodeValid_prime [2, 23, 101, 12161] ⟨56500007, 5, [(2, 1), (23, 1), (101, 1), (12161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_101
    · exact prime_12161
  · decide +kernel

theorem prime_60917921 : Nat.Prime 60917921 := by
  apply nodeValid_prime [2, 5, 7, 109, 499] ⟨60917921, 3, [(2, 5), (5, 1), (7, 1), (109, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_109
    · exact prime_499
  · decide +kernel

theorem prime_62352163 : Nat.Prime 62352163 := by
  apply nodeValid_prime [2, 3, 883, 3923] ⟨62352163, 3, [(2, 1), (3, 2), (883, 1), (3923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_883
    · exact prime_3923
  · decide +kernel

theorem prime_79220417 : Nat.Prime 79220417 := by
  apply nodeValid_prime [2, 11, 131, 859] ⟨79220417, 3, [(2, 6), (11, 1), (131, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_131
    · exact prime_859
  · decide +kernel

theorem prime_104423173 : Nat.Prime 104423173 := by
  apply nodeValid_prime [2, 3, 7, 1243133] ⟨104423173, 6, [(2, 2), (3, 1), (7, 1), (1243133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1243133
  · decide +kernel

theorem prime_118144277 : Nat.Prime 118144277 := by
  apply nodeValid_prime [2, 47, 628427] ⟨118144277, 2, [(2, 2), (47, 1), (628427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_628427
  · decide +kernel

theorem prime_155031797 : Nat.Prime 155031797 := by
  apply nodeValid_prime [2, 29, 1336481] ⟨155031797, 2, [(2, 2), (29, 1), (1336481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1336481
  · decide +kernel

theorem prime_236224799 : Nat.Prime 236224799 := by
  apply nodeValid_prime [2, 37, 3192227] ⟨236224799, 13, [(2, 1), (37, 1), (3192227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_3192227
  · decide +kernel

theorem prime_295971971 : Nat.Prime 295971971 := by
  apply nodeValid_prime [2, 5, 7, 29, 145799] ⟨295971971, 7, [(2, 1), (5, 1), (7, 1), (29, 1), (145799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_29
    · exact prime_145799
  · decide +kernel

theorem prime_316331947 : Nat.Prime 316331947 := by
  apply nodeValid_prime [2, 3, 7, 119551] ⟨316331947, 3, [(2, 1), (3, 3), (7, 2), (119551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_119551
  · decide +kernel

theorem prime_373563209 : Nat.Prime 373563209 := by
  apply nodeValid_prime [2, 46695401] ⟨373563209, 3, [(2, 3), (46695401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_46695401
  · decide +kernel

theorem prime_374112979 : Nat.Prime 374112979 := by
  apply nodeValid_prime [2, 3, 62352163] ⟨374112979, 2, [(2, 1), (3, 1), (62352163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62352163
  · decide +kernel

theorem prime_432950291 : Nat.Prime 432950291 := by
  apply nodeValid_prime [2, 5, 89, 227, 2143] ⟨432950291, 2, [(2, 1), (5, 1), (89, 1), (227, 1), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_227
    · exact prime_2143
  · decide +kernel

theorem prime_440220479 : Nat.Prime 440220479 := by
  apply nodeValid_prime [2, 1367, 161017] ⟨440220479, 17, [(2, 1), (1367, 1), (161017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1367
    · exact prime_161017
  · decide +kernel

theorem prime_448208777 : Nat.Prime 448208777 := by
  apply nodeValid_prime [2, 227, 246811] ⟨448208777, 3, [(2, 3), (227, 1), (246811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_246811
  · decide +kernel

theorem prime_472449599 : Nat.Prime 472449599 := by
  apply nodeValid_prime [2, 236224799] ⟨472449599, 13, [(2, 1), (236224799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_236224799
  · decide +kernel

theorem prime_504144397 : Nat.Prime 504144397 := by
  apply nodeValid_prime [2, 3, 7, 2000573] ⟨504144397, 5, [(2, 2), (3, 2), (7, 1), (2000573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2000573
  · decide +kernel

theorem prime_591943943 : Nat.Prime 591943943 := by
  apply nodeValid_prime [2, 295971971] ⟨591943943, 5, [(2, 1), (295971971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_295971971
  · decide +kernel

theorem prime_633763337 : Nat.Prime 633763337 := by
  apply nodeValid_prime [2, 79220417] ⟨633763337, 3, [(2, 3), (79220417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_79220417
  · decide +kernel

theorem prime_1036456217 : Nat.Prime 1036456217 := by
  apply nodeValid_prime [2, 383, 338269] ⟨1036456217, 3, [(2, 3), (383, 1), (338269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_338269
  · decide +kernel

theorem prime_1302770437 : Nat.Prime 1302770437 := by
  apply nodeValid_prime [2, 3, 11, 1637, 6029] ⟨1302770437, 2, [(2, 2), (3, 1), (11, 1), (1637, 1), (6029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1637
    · exact prime_6029
  · decide +kernel

theorem prime_2179162501 : Nat.Prime 2179162501 := by
  apply nodeValid_prime [2, 3, 5, 58111] ⟨2179162501, 2, [(2, 2), (3, 1), (5, 5), (58111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_58111
  · decide +kernel

theorem prime_2973259711 : Nat.Prime 2973259711 := by
  apply nodeValid_prime [2, 3, 5, 17, 263, 821] ⟨2973259711, 3, [(2, 1), (3, 4), (5, 1), (17, 1), (263, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_263
    · exact prime_821
  · decide +kernel

theorem prime_3006125359 : Nat.Prime 3006125359 := by
  apply nodeValid_prime [2, 3, 47, 733, 14543] ⟨3006125359, 3, [(2, 1), (3, 1), (47, 1), (733, 1), (14543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_733
    · exact prime_14543
  · decide +kernel

theorem prime_3036485729 : Nat.Prime 3036485729 := by
  apply nodeValid_prime [2, 1319, 71941] ⟨3036485729, 3, [(2, 5), (1319, 1), (71941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1319
    · exact prime_71941
  · decide +kernel

theorem prime_3071751203 : Nat.Prime 3071751203 := by
  apply nodeValid_prime [2, 13, 118144277] ⟨3071751203, 2, [(2, 1), (13, 1), (118144277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_118144277
  · decide +kernel

theorem prime_3263989483 : Nat.Prime 3263989483 := by
  apply nodeValid_prime [2, 3, 13, 647, 21559] ⟨3263989483, 2, [(2, 1), (3, 2), (13, 1), (647, 1), (21559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_647
    · exact prime_21559
  · decide +kernel

theorem prime_3868983961 : Nat.Prime 3868983961 := by
  apply nodeValid_prime [2, 3, 5, 29, 269, 4133] ⟨3868983961, 11, [(2, 3), (3, 1), (5, 1), (29, 1), (269, 1), (4133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_269
    · exact prime_4133
  · decide +kernel

theorem prime_6072971459 : Nat.Prime 6072971459 := by
  apply nodeValid_prime [2, 3036485729] ⟨6072971459, 2, [(2, 1), (3036485729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3036485729
  · decide +kernel

theorem prime_6751728229 : Nat.Prime 6751728229 := by
  apply nodeValid_prime [2, 3, 7, 17, 509, 1327] ⟨6751728229, 2, [(2, 2), (3, 1), (7, 2), (17, 1), (509, 1), (1327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_509
    · exact prime_1327
  · decide +kernel

theorem prime_7424691971 : Nat.Prime 7424691971 := by
  apply nodeValid_prime [2, 5, 10169, 73013] ⟨7424691971, 2, [(2, 1), (5, 1), (10169, 1), (73013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10169
    · exact prime_73013
  · decide +kernel

theorem prime_8965517017 : Nat.Prime 8965517017 := by
  apply nodeValid_prime [2, 3, 373563209] ⟨8965517017, 5, [(2, 3), (3, 1), (373563209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_373563209
  · decide +kernel

theorem prime_10643624903 : Nat.Prime 10643624903 := by
  apply nodeValid_prime [2, 4243, 1254257] ⟨10643624903, 5, [(2, 1), (4243, 1), (1254257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4243
    · exact prime_1254257
  · decide +kernel

theorem prime_14113072469 : Nat.Prime 14113072469 := by
  apply nodeValid_prime [2, 11, 3631, 88337] ⟨14113072469, 3, [(2, 2), (11, 1), (3631, 1), (88337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3631
    · exact prime_88337
  · decide +kernel

theorem prime_22249259573 : Nat.Prime 22249259573 := by
  apply nodeValid_prime [2, 431, 12905603] ⟨22249259573, 2, [(2, 2), (431, 1), (12905603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_12905603
  · decide +kernel

theorem prime_22597739081 : Nat.Prime 22597739081 := by
  apply nodeValid_prime [2, 5, 7, 3347, 24113] ⟨22597739081, 3, [(2, 3), (5, 1), (7, 1), (3347, 1), (24113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3347
    · exact prime_24113
  · decide +kernel

theorem prime_27890219573 : Nat.Prime 27890219573 := by
  apply nodeValid_prime [2, 191, 2111, 17293] ⟨27890219573, 2, [(2, 2), (191, 1), (2111, 1), (17293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_191
    · exact prime_2111
    · exact prime_17293
  · decide +kernel

theorem prime_41776318289 : Nat.Prime 41776318289 := by
  apply nodeValid_prime [2, 83, 1117, 28163] ⟨41776318289, 3, [(2, 4), (83, 1), (1117, 1), (28163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_1117
    · exact prime_28163
  · decide +kernel

theorem prime_139549525541 : Nat.Prime 139549525541 := by
  apply nodeValid_prime [2, 5, 17, 61, 6728521] ⟨139549525541, 2, [(2, 2), (5, 1), (17, 1), (61, 1), (6728521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_61
    · exact prime_6728521
  · decide +kernel

theorem prime_145103866783 : Nat.Prime 145103866783 := by
  apply nodeValid_prime [2, 3, 7, 41, 181, 465551] ⟨145103866783, 3, [(2, 1), (3, 1), (7, 1), (41, 1), (181, 1), (465551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_181
    · exact prime_465551
  · decide +kernel

theorem prime_196733257933 : Nat.Prime 196733257933 := by
  apply nodeValid_prime [2, 3, 157, 104423173] ⟨196733257933, 5, [(2, 2), (3, 1), (157, 1), (104423173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_104423173
  · decide +kernel

theorem prime_209324288813 : Nat.Prime 209324288813 := by
  apply nodeValid_prime [2, 2837, 18445919] ⟨209324288813, 2, [(2, 2), (2837, 1), (18445919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2837
    · exact prime_18445919
  · decide +kernel

theorem prime_259634407427 : Nat.Prime 259634407427 := by
  apply nodeValid_prime [2, 347, 374112979] ⟨259634407427, 2, [(2, 1), (347, 1), (374112979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_374112979
  · decide +kernel

theorem prime_279099051083 : Nat.Prime 279099051083 := by
  apply nodeValid_prime [2, 139549525541] ⟨279099051083, 2, [(2, 1), (139549525541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_139549525541
  · decide +kernel

theorem prime_558986051471 : Nat.Prime 558986051471 := by
  apply nodeValid_prime [2, 5, 7, 11, 157, 739, 6257] ⟨558986051471, 11, [(2, 1), (5, 1), (7, 1), (11, 1), (157, 1), (739, 1), (6257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_157
    · exact prime_739
    · exact prime_6257
  · decide +kernel

theorem prime_559380326221 : Nat.Prime 559380326221 := by
  apply nodeValid_prime [2, 3, 5, 443, 2338351] ⟨559380326221, 6, [(2, 2), (3, 3), (5, 1), (443, 1), (2338351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_443
    · exact prime_2338351
  · decide +kernel

theorem prime_562541212943 : Nat.Prime 562541212943 := by
  apply nodeValid_prime [2, 37, 3637, 2090159] ⟨562541212943, 5, [(2, 1), (37, 1), (3637, 1), (2090159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_3637
    · exact prime_2090159
  · decide +kernel

theorem prime_835526365781 : Nat.Prime 835526365781 := by
  apply nodeValid_prime [2, 5, 41776318289] ⟨835526365781, 2, [(2, 2), (5, 1), (41776318289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41776318289
  · decide +kernel

theorem prime_1669873352347 : Nat.Prime 1669873352347 := by
  apply nodeValid_prime [2, 3, 3457, 8945207] ⟨1669873352347, 3, [(2, 1), (3, 3), (3457, 1), (8945207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3457
    · exact prime_8945207
  · decide +kernel

theorem prime_6674777871901 : Nat.Prime 6674777871901 := by
  apply nodeValid_prime [2, 3, 5, 22249259573] ⟨6674777871901, 2, [(2, 2), (3, 1), (5, 2), (22249259573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22249259573
  · decide +kernel

theorem prime_6674777872019 : Nat.Prime 6674777872019 := by
  apply nodeValid_prime [2, 23, 145103866783] ⟨6674777872019, 2, [(2, 1), (23, 1), (145103866783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_145103866783
  · decide +kernel

theorem prime_6674778037481 : Nat.Prime 6674778037481 := by
  apply nodeValid_prime [2, 5, 7, 23, 1036456217] ⟨6674778037481, 6, [(2, 3), (5, 1), (7, 1), (23, 1), (1036456217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_1036456217
  · decide +kernel

theorem prime_6679493363771 : Nat.Prime 6679493363771 := by
  apply nodeValid_prime [2, 5, 7069, 7393, 12781] ⟨6679493363771, 2, [(2, 1), (5, 1), (7069, 1), (7393, 1), (12781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7069
    · exact prime_7393
    · exact prime_12781
  · decide +kernel

theorem prime_6679493409389 : Nat.Prime 6679493409389 := by
  apply nodeValid_prime [2, 1669873352347] ⟨6679493409389, 2, [(2, 2), (1669873352347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1669873352347
  · decide +kernel

theorem prime_6679493410013 : Nat.Prime 6679493410013 := by
  apply nodeValid_prime [2, 71, 1367, 2677, 6427] ⟨6679493410013, 2, [(2, 2), (71, 1), (1367, 1), (2677, 1), (6427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1367
    · exact prime_2677
    · exact prime_6427
  · decide +kernel

theorem prime_6684210925519 : Nat.Prime 6684210925519 := by
  apply nodeValid_prime [2, 3, 7, 59, 1543, 1748167] ⟨6684210925519, 7, [(2, 1), (3, 1), (7, 1), (59, 1), (1543, 1), (1748167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_1543
    · exact prime_1748167
  · decide +kernel

theorem prime_6684210926249 : Nat.Prime 6684210926249 := by
  apply nodeValid_prime [2, 835526365781] ⟨6684210926249, 3, [(2, 3), (835526365781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_835526365781
  · decide +kernel

theorem prime_6684210946711 : Nat.Prime 6684210946711 := by
  apply nodeValid_prime [2, 3, 5, 11, 6751728229] ⟨6684210946711, 12, [(2, 1), (3, 2), (5, 1), (11, 1), (6751728229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_6751728229
  · decide +kernel

theorem prime_6688930767977 : Nat.Prime 6688930767977 := by
  apply nodeValid_prime [2, 37, 22597739081] ⟨6688930767977, 3, [(2, 3), (37, 1), (22597739081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_22597739081
  · decide +kernel

theorem prime_6688930769723 : Nat.Prime 6688930769723 := by
  apply nodeValid_prime [2, 17, 196733257933] ⟨6688930769723, 2, [(2, 1), (17, 1), (196733257933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_196733257933
  · decide +kernel

theorem prime_6688930776623 : Nat.Prime 6688930776623 := by
  apply nodeValid_prime [2, 311, 35963, 299027] ⟨6688930776623, 5, [(2, 1), (311, 1), (35963, 1), (299027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_35963
    · exact prime_299027
  · decide +kernel

theorem prime_6693652697521 : Nat.Prime 6693652697521 := by
  apply nodeValid_prime [2, 3, 5, 27890219573] ⟨6693652697521, 21, [(2, 4), (3, 1), (5, 1), (27890219573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_27890219573
  · decide +kernel

theorem prime_6693652698643 : Nat.Prime 6693652698643 := by
  apply nodeValid_prime [2, 3, 7, 13, 29, 10839467] ⟨6693652698643, 3, [(2, 1), (3, 2), (7, 1), (13, 2), (29, 1), (10839467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_10839467
  · decide +kernel

theorem prime_6693652867273 : Nat.Prime 6693652867273 := by
  apply nodeValid_prime [2, 3, 7, 257, 155031797] ⟨6693652867273, 5, [(2, 3), (3, 1), (7, 1), (257, 1), (155031797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_257
    · exact prime_155031797
  · decide +kernel

theorem prime_6698377225993 : Nat.Prime 6698377225993 := by
  apply nodeValid_prime [2, 3, 279099051083] ⟨6698377225993, 5, [(2, 3), (3, 1), (279099051083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_279099051083
  · decide +kernel

theorem prime_6698377242017 : Nat.Prime 6698377242017 := by
  apply nodeValid_prime [2, 209324288813] ⟨6698377242017, 3, [(2, 5), (209324288813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_209324288813
  · decide +kernel

theorem prime_6698377242653 : Nat.Prime 6698377242653 := by
  apply nodeValid_prime [2, 677, 34757, 71167] ⟨6698377242653, 2, [(2, 2), (677, 1), (34757, 1), (71167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_677
    · exact prime_34757
    · exact prime_71167
  · decide +kernel

theorem prime_6703103853077 : Nat.Prime 6703103853077 := by
  apply nodeValid_prime [2, 769, 2179162501] ⟨6703103853077, 2, [(2, 2), (769, 1), (2179162501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_769
    · exact prime_2179162501
  · decide +kernel

theorem prime_6703103902513 : Nat.Prime 6703103902513 := by
  apply nodeValid_prime [2, 3, 277, 504144397] ⟨6703103902513, 10, [(2, 4), (3, 1), (277, 1), (504144397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_277
    · exact prime_504144397
  · decide +kernel

theorem prime_6707832616483 : Nat.Prime 6707832616483 := by
  apply nodeValid_prime [2, 3, 73, 719, 3833, 5557] ⟨6707832616483, 2, [(2, 1), (3, 1), (73, 1), (719, 1), (3833, 1), (5557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_719
    · exact prime_3833
    · exact prime_5557
  · decide +kernel

theorem prime_6707832617653 : Nat.Prime 6707832617653 := by
  apply nodeValid_prime [2, 3, 558986051471] ⟨6707832617653, 2, [(2, 2), (3, 1), (558986051471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_558986051471
  · decide +kernel

theorem prime_6707832744661 : Nat.Prime 6707832744661 := by
  apply nodeValid_prime [2, 3, 5, 13721, 8147891] ⟨6707832744661, 2, [(2, 2), (3, 1), (5, 1), (13721, 1), (8147891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13721
    · exact prime_8147891
  · decide +kernel

theorem prime_6712563902593 : Nat.Prime 6712563902593 := by
  apply nodeValid_prime [2, 3, 37, 472449599] ⟨6712563902593, 7, [(2, 7), (3, 1), (37, 1), (472449599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_472449599
  · decide +kernel

theorem prime_6712563914653 : Nat.Prime 6712563914653 := by
  apply nodeValid_prime [2, 3, 559380326221] ⟨6712563914653, 5, [(2, 2), (3, 1), (559380326221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_559380326221
  · decide +kernel

theorem prime_6712563915341 : Nat.Prime 6712563915341 := by
  apply nodeValid_prime [2, 5, 1061, 316331947] ⟨6712563915341, 3, [(2, 2), (5, 1), (1061, 1), (316331947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1061
    · exact prime_316331947
  · decide +kernel

theorem prime_6717297312829 : Nat.Prime 6717297312829 := by
  apply nodeValid_prime [2, 3, 1021, 60917921] ⟨6717297312829, 7, [(2, 2), (3, 3), (1021, 1), (60917921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1021
    · exact prime_60917921
  · decide +kernel

theorem prime_6717297348061 : Nat.Prime 6717297348061 := by
  apply nodeValid_prime [2, 3, 5, 13, 6323, 1361999] ⟨6717297348061, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (6323, 1), (1361999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_6323
    · exact prime_1361999
  · decide +kernel

theorem prime_6717297350191 : Nat.Prime 6717297350191 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 29, 2729, 17573] ⟨6717297350191, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (29, 1), (2729, 1), (17573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_29
    · exact prime_2729
    · exact prime_17573
  · decide +kernel

theorem prime_6722032936051 : Nat.Prime 6722032936051 := by
  apply nodeValid_prime [2, 3, 5, 43, 587, 13763] ⟨6722032936051, 2, [(2, 1), (3, 2), (5, 2), (43, 2), (587, 1), (13763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_587
    · exact prime_13763
  · decide +kernel

theorem prime_6722032936387 : Nat.Prime 6722032936387 := by
  apply nodeValid_prime [2, 3, 23, 78989, 616673] ⟨6722032936387, 3, [(2, 1), (3, 1), (23, 1), (78989, 1), (616673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_78989
    · exact prime_616673
  · decide +kernel

theorem prime_6722032994879 : Nat.Prime 6722032994879 := by
  apply nodeValid_prime [2, 391283, 8589733] ⟨6722032994879, 11, [(2, 1), (391283, 1), (8589733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_391283
    · exact prime_8589733
  · decide +kernel

theorem prime_6726770925727 : Nat.Prime 6726770925727 := by
  apply nodeValid_prime [2, 3, 151, 7424691971] ⟨6726770925727, 5, [(2, 1), (3, 1), (151, 1), (7424691971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_7424691971
  · decide +kernel

theorem prime_6726770926201 : Nat.Prime 6726770926201 := by
  apply nodeValid_prime [2, 3, 5, 13, 89, 3229987] ⟨6726770926201, 17, [(2, 3), (3, 2), (5, 2), (13, 1), (89, 1), (3229987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_89
    · exact prime_3229987
  · decide +kernel

theorem prime_6726770938697 : Nat.Prime 6726770938697 := by
  apply nodeValid_prime [2, 79, 10643624903] ⟨6726770938697, 3, [(2, 3), (79, 1), (10643624903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_10643624903
  · decide +kernel

theorem prime_6731511123581 : Nat.Prime 6731511123581 := by
  apply nodeValid_prime [2, 5, 35257, 9546347] ⟨6731511123581, 2, [(2, 2), (5, 1), (35257, 1), (9546347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_35257
    · exact prime_9546347
  · decide +kernel

theorem prime_6731511124469 : Nat.Prime 6731511124469 := by
  apply nodeValid_prime [2, 13, 23, 432950291] ⟨6731511124469, 2, [(2, 2), (13, 2), (23, 1), (432950291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_432950291
  · decide +kernel

theorem prime_6731511144131 : Nat.Prime 6731511144131 := by
  apply nodeValid_prime [2, 5, 137941, 4879993] ⟨6731511144131, 2, [(2, 1), (5, 1), (137941, 1), (4879993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137941
    · exact prime_4879993
  · decide +kernel

theorem prime_6736253604211 : Nat.Prime 6736253604211 := by
  apply nodeValid_prime [2, 3, 5, 13, 16811, 114161] ⟨6736253604211, 3, [(2, 1), (3, 3), (5, 1), (13, 1), (16811, 1), (114161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_16811
    · exact prime_114161
  · decide +kernel

theorem prime_6736253767637 : Nat.Prime 6736253767637 := by
  apply nodeValid_prime [2, 167, 91393, 110339] ⟨6736253767637, 2, [(2, 2), (167, 1), (91393, 1), (110339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_91393
    · exact prime_110339
  · decide +kernel

theorem prime_6736253769659 : Nat.Prime 6736253769659 := by
  apply nodeValid_prime [2, 7, 1093, 440220479] ⟨6736253769659, 2, [(2, 1), (7, 1), (1093, 1), (440220479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1093
    · exact prime_440220479
  · decide +kernel

theorem prime_6740998319491 : Nat.Prime 6740998319491 := by
  apply nodeValid_prime [2, 3, 5, 37, 6072971459] ⟨6740998319491, 15, [(2, 1), (3, 1), (5, 1), (37, 1), (6072971459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_6072971459
  · decide +kernel

theorem prime_6740998350041 : Nat.Prime 6740998350041 := by
  apply nodeValid_prime [2, 5, 109, 4157, 371927] ⟨6740998350041, 3, [(2, 3), (5, 1), (109, 1), (4157, 1), (371927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_4157
    · exact prime_371927
  · decide +kernel

theorem prime_6740998350881 : Nat.Prime 6740998350881 := by
  apply nodeValid_prime [2, 5, 5189, 8119337] ⟨6740998350881, 3, [(2, 5), (5, 1), (5189, 1), (8119337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5189
    · exact prime_8119337
  · decide +kernel

theorem prime_6745745305597 : Nat.Prime 6745745305597 := by
  apply nodeValid_prime [2, 3, 11, 17, 3006125359] ⟨6745745305597, 2, [(2, 2), (3, 1), (11, 1), (17, 1), (3006125359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_3006125359
  · decide +kernel

theorem prime_6745745321851 : Nat.Prime 6745745321851 := by
  apply nodeValid_prime [2, 3, 5, 29, 17683, 87697] ⟨6745745321851, 7, [(2, 1), (3, 1), (5, 2), (29, 1), (17683, 1), (87697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_17683
    · exact prime_87697
  · decide +kernel

theorem prime_6745745322787 : Nat.Prime 6745745322787 := by
  apply nodeValid_prime [2, 3, 863, 1302770437] ⟨6745745322787, 2, [(2, 1), (3, 1), (863, 1), (1302770437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_863
    · exact prime_1302770437
  · decide +kernel

theorem prime_6750494555317 : Nat.Prime 6750494555317 := by
  apply nodeValid_prime [2, 3, 562541212943] ⟨6750494555317, 6, [(2, 2), (3, 1), (562541212943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_562541212943
  · decide +kernel

theorem prime_6750494592967 : Nat.Prime 6750494592967 := by
  apply nodeValid_prime [2, 3, 4397, 28430557] ⟨6750494592967, 3, [(2, 1), (3, 3), (4397, 1), (28430557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4397
    · exact prime_28430557
  · decide +kernel

theorem prime_6750494593103 : Nat.Prime 6750494593103 := by
  apply nodeValid_prime [2, 13, 259634407427] ⟨6750494593103, 7, [(2, 1), (13, 1), (259634407427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_259634407427
  · decide +kernel

theorem prime_6755245994807 : Nat.Prime 6755245994807 := by
  apply nodeValid_prime [2, 71, 163, 929, 314159] ⟨6755245994807, 5, [(2, 1), (71, 1), (163, 1), (929, 1), (314159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_163
    · exact prime_929
    · exact prime_314159
  · decide +kernel

theorem prime_6755245995907 : Nat.Prime 6755245995907 := by
  apply nodeValid_prime [2, 3, 97, 3868983961] ⟨6755245995907, 2, [(2, 1), (3, 2), (97, 1), (3868983961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_3868983961
  · decide +kernel

theorem prime_6755246063393 : Nat.Prime 6755246063393 := by
  apply nodeValid_prime [2, 71, 2973259711] ⟨6755246063393, 3, [(2, 5), (71, 1), (2973259711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_2973259711
  · decide +kernel

theorem prime_6759999829061 : Nat.Prime 6759999829061 := by
  apply nodeValid_prime [2, 5, 571, 591943943] ⟨6759999829061, 3, [(2, 2), (5, 1), (571, 1), (591943943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_571
    · exact prime_591943943
  · decide +kernel

theorem prime_6759999830819 : Nat.Prime 6759999830819 := by
  apply nodeValid_prime [2, 13, 29, 8965517017] ⟨6759999830819, 2, [(2, 1), (13, 1), (29, 1), (8965517017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_8965517017
  · decide +kernel

theorem prime_6759999837523 : Nat.Prime 6759999837523 := by
  apply nodeValid_prime [2, 3, 17, 23, 56500007] ⟨6759999837523, 3, [(2, 1), (3, 2), (17, 2), (23, 1), (56500007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_56500007
  · decide +kernel

theorem prime_6764755885457 : Nat.Prime 6764755885457 := by
  apply nodeValid_prime [2, 21341, 19811501] ⟨6764755885457, 3, [(2, 4), (21341, 1), (19811501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21341
    · exact prime_19811501
  · decide +kernel

theorem prime_6764755893817 : Nat.Prime 6764755893817 := by
  apply nodeValid_prime [2, 3, 7933, 35530673] ⟨6764755893817, 5, [(2, 3), (3, 1), (7933, 1), (35530673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7933
    · exact prime_35530673
  · decide +kernel

theorem prime_6764755894111 : Nat.Prime 6764755894111 := by
  apply nodeValid_prime [2, 3, 5, 14419, 5212841] ⟨6764755894111, 6, [(2, 1), (3, 2), (5, 1), (14419, 1), (5212841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14419
    · exact prime_5212841
  · decide +kernel

theorem prime_6769514186389 : Nat.Prime 6769514186389 := by
  apply nodeValid_prime [2, 3, 23, 449, 1979, 3067] ⟨6769514186389, 2, [(2, 2), (3, 3), (23, 1), (449, 1), (1979, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_449
    · exact prime_1979
    · exact prime_3067
  · decide +kernel

theorem prime_6769514187743 : Nat.Prime 6769514187743 := by
  apply nodeValid_prime [2, 17, 61, 3263989483] ⟨6769514187743, 5, [(2, 1), (17, 1), (61, 1), (3263989483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_61
    · exact prime_3263989483
  · decide +kernel

theorem prime_6769514199713 : Nat.Prime 6769514199713 := by
  apply nodeValid_prime [2, 11, 29, 41, 43, 376153] ⟨6769514199713, 3, [(2, 5), (11, 1), (29, 1), (41, 1), (43, 1), (376153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_41
    · exact prime_43
    · exact prime_376153
  · decide +kernel

theorem prime_6774274743199 : Nat.Prime 6774274743199 := by
  apply nodeValid_prime [2, 3, 62207, 18149819] ⟨6774274743199, 6, [(2, 1), (3, 1), (62207, 1), (18149819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_62207
    · exact prime_18149819
  · decide +kernel

theorem prime_6774274785121 : Nat.Prime 6774274785121 := by
  apply nodeValid_prime [2, 3, 5, 14113072469] ⟨6774274785121, 11, [(2, 5), (3, 1), (5, 1), (14113072469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14113072469
  · decide +kernel

theorem prime_6779037639797 : Nat.Prime 6779037639797 := by
  apply nodeValid_prime [2, 17, 37, 1373, 1962397] ⟨6779037639797, 2, [(2, 2), (17, 1), (37, 1), (1373, 1), (1962397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_1373
    · exact prime_1962397
  · decide +kernel

theorem prime_6779037656977 : Nat.Prime 6779037656977 := by
  apply nodeValid_prime [2, 3, 13, 31, 9431, 37159] ⟨6779037656977, 5, [(2, 4), (3, 1), (13, 1), (31, 1), (9431, 1), (37159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_9431
    · exact prime_37159
  · decide +kernel

theorem prime_6779037657247 : Nat.Prime 6779037657247 := by
  apply nodeValid_prime [2, 3, 429563, 2630207] ⟨6779037657247, 3, [(2, 1), (3, 1), (429563, 1), (2630207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_429563
    · exact prime_2630207
  · decide +kernel

theorem prime_6783802759249 : Nat.Prime 6783802759249 := by
  apply nodeValid_prime [2, 3, 223, 633763337] ⟨6783802759249, 11, [(2, 4), (3, 1), (223, 1), (633763337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_633763337
  · decide +kernel

theorem prime_6783802798343 : Nat.Prime 6783802798343 := by
  apply nodeValid_prime [2, 23, 53, 79, 35221871] ⟨6783802798343, 5, [(2, 1), (23, 1), (53, 1), (79, 1), (35221871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_53
    · exact prime_79
    · exact prime_35221871
  · decide +kernel

theorem prime_6783802798351 : Nat.Prime 6783802798351 := by
  apply nodeValid_prime [2, 3, 5, 28537, 1584797] ⟨6783802798351, 13, [(2, 1), (3, 1), (5, 2), (28537, 1), (1584797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28537
    · exact prime_1584797
  · decide +kernel

theorem prime_6788570136443 : Nat.Prime 6788570136443 := by
  apply nodeValid_prime [2, 7573, 448208777] ⟨6788570136443, 2, [(2, 1), (7573, 1), (448208777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7573
    · exact prime_448208777
  · decide +kernel

theorem prime_6788570157563 : Nat.Prime 6788570157563 := by
  apply nodeValid_prime [2, 151, 20789, 1081279] ⟨6788570157563, 2, [(2, 1), (151, 1), (20789, 1), (1081279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_20789
    · exact prime_1081279
  · decide +kernel

theorem prime_6788570158631 : Nat.Prime 6788570158631 := by
  apply nodeValid_prime [2, 5, 13, 17, 3071751203] ⟨6788570158631, 7, [(2, 1), (5, 1), (13, 1), (17, 1), (3071751203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_3071751203
  · decide +kernel

end Sude.Lucas.Generated
