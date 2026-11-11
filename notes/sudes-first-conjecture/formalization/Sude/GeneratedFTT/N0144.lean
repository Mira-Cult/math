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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0109
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0115
import Sude.GeneratedFTT.N0122
import Sude.GeneratedFTT.N0136
import Sude.GeneratedFTT.N0142
import Sude.GeneratedFTT.N0143

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10657 : Nat.Prime 10657 := by
  apply nodeValid_prime [2, 3, 37] ⟨10657, 7, [(2, 5), (3, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_13331 : Nat.Prime 13331 := by
  apply nodeValid_prime [2, 5, 31, 43] ⟨13331, 2, [(2, 1), (5, 1), (31, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_43
  · decide +kernel

theorem prime_22063 : Nat.Prime 22063 := by
  apply nodeValid_prime [2, 3, 3677] ⟨22063, 5, [(2, 1), (3, 1), (3677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3677
  · decide +kernel

theorem prime_25409 : Nat.Prime 25409 := by
  apply nodeValid_prime [2, 397] ⟨25409, 3, [(2, 6), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_397
  · decide +kernel

theorem prime_26297 : Nat.Prime 26297 := by
  apply nodeValid_prime [2, 19, 173] ⟨26297, 3, [(2, 3), (19, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_173
  · decide +kernel

theorem prime_29303 : Nat.Prime 29303 := by
  apply nodeValid_prime [2, 7, 13, 23] ⟨29303, 7, [(2, 1), (7, 2), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_32939 : Nat.Prime 32939 := by
  apply nodeValid_prime [2, 43, 383] ⟨32939, 2, [(2, 1), (43, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_383
  · decide +kernel

theorem prime_57373 : Nat.Prime 57373 := by
  apply nodeValid_prime [2, 3, 7, 683] ⟨57373, 2, [(2, 2), (3, 1), (7, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_683
  · decide +kernel

theorem prime_59023 : Nat.Prime 59023 := by
  apply nodeValid_prime [2, 3, 1093] ⟨59023, 5, [(2, 1), (3, 3), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1093
  · decide +kernel

theorem prime_69239 : Nat.Prime 69239 := by
  apply nodeValid_prime [2, 13, 2663] ⟨69239, 7, [(2, 1), (13, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2663
  · decide +kernel

theorem prime_73553 : Nat.Prime 73553 := by
  apply nodeValid_prime [2, 4597] ⟨73553, 3, [(2, 4), (4597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4597
  · decide +kernel

theorem prime_79633 : Nat.Prime 79633 := by
  apply nodeValid_prime [2, 3, 7, 79] ⟨79633, 13, [(2, 4), (3, 2), (7, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
  · decide +kernel

theorem prime_82009 : Nat.Prime 82009 := by
  apply nodeValid_prime [2, 3, 17, 67] ⟨82009, 13, [(2, 3), (3, 2), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_82837 : Nat.Prime 82837 := by
  apply nodeValid_prime [2, 3, 13, 59] ⟨82837, 2, [(2, 2), (3, 3), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_88241 : Nat.Prime 88241 := by
  apply nodeValid_prime [2, 5, 1103] ⟨88241, 3, [(2, 4), (5, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1103
  · decide +kernel

theorem prime_90847 : Nat.Prime 90847 := by
  apply nodeValid_prime [2, 3, 7, 103] ⟨90847, 5, [(2, 1), (3, 2), (7, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
  · decide +kernel

theorem prime_106649 : Nat.Prime 106649 := by
  apply nodeValid_prime [2, 13331] ⟨106649, 3, [(2, 3), (13331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13331
  · decide +kernel

theorem prime_115849 : Nat.Prime 115849 := by
  apply nodeValid_prime [2, 3, 1609] ⟨115849, 13, [(2, 3), (3, 2), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1609
  · decide +kernel

theorem prime_147107 : Nat.Prime 147107 := by
  apply nodeValid_prime [2, 73553] ⟨147107, 2, [(2, 1), (73553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_73553
  · decide +kernel

theorem prime_148639 : Nat.Prime 148639 := by
  apply nodeValid_prime [2, 3, 7, 3539] ⟨148639, 3, [(2, 1), (3, 1), (7, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3539
  · decide +kernel

theorem prime_148867 : Nat.Prime 148867 := by
  apply nodeValid_prime [2, 3, 43, 577] ⟨148867, 3, [(2, 1), (3, 1), (43, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_577
  · decide +kernel

theorem prime_180073 : Nat.Prime 180073 := by
  apply nodeValid_prime [2, 3, 41, 61] ⟨180073, 7, [(2, 3), (3, 2), (41, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_61
  · decide +kernel

theorem prime_181183 : Nat.Prime 181183 := by
  apply nodeValid_prime [2, 3, 30197] ⟨181183, 3, [(2, 1), (3, 1), (30197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30197
  · decide +kernel

theorem prime_186271 : Nat.Prime 186271 := by
  apply nodeValid_prime [2, 3, 5, 7, 887] ⟨186271, 12, [(2, 1), (3, 1), (5, 1), (7, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_887
  · decide +kernel

theorem prime_188677 : Nat.Prime 188677 := by
  apply nodeValid_prime [2, 3, 1747] ⟨188677, 2, [(2, 2), (3, 3), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1747
  · decide +kernel

theorem prime_219103 : Nat.Prime 219103 := by
  apply nodeValid_prime [2, 3, 13, 53] ⟨219103, 6, [(2, 1), (3, 1), (13, 1), (53, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
  · decide +kernel

theorem prime_223837 : Nat.Prime 223837 := by
  apply nodeValid_prime [2, 3, 23, 811] ⟨223837, 5, [(2, 2), (3, 1), (23, 1), (811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_811
  · decide +kernel

theorem prime_229393 : Nat.Prime 229393 := by
  apply nodeValid_prime [2, 3, 59] ⟨229393, 5, [(2, 4), (3, 5), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_232907 : Nat.Prime 232907 := by
  apply nodeValid_prime [2, 101, 1153] ⟨232907, 2, [(2, 1), (101, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_1153
  · decide +kernel

theorem prime_236729 : Nat.Prime 236729 := by
  apply nodeValid_prime [2, 127, 233] ⟨236729, 3, [(2, 3), (127, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_233
  · decide +kernel

theorem prime_291547 : Nat.Prime 291547 := by
  apply nodeValid_prime [2, 3, 5399] ⟨291547, 5, [(2, 1), (3, 3), (5399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5399
  · decide +kernel

theorem prime_355609 : Nat.Prime 355609 := by
  apply nodeValid_prime [2, 3, 11, 449] ⟨355609, 26, [(2, 3), (3, 2), (11, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_449
  · decide +kernel

theorem prime_371353 : Nat.Prime 371353 := by
  apply nodeValid_prime [2, 3, 15473] ⟨371353, 5, [(2, 3), (3, 1), (15473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15473
  · decide +kernel

theorem prime_462589 : Nat.Prime 462589 := by
  apply nodeValid_prime [2, 3, 7, 5507] ⟨462589, 6, [(2, 2), (3, 1), (7, 1), (5507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5507
  · decide +kernel

theorem prime_536279 : Nat.Prime 536279 := by
  apply nodeValid_prime [2, 37, 7247] ⟨536279, 7, [(2, 1), (37, 1), (7247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_7247
  · decide +kernel

theorem prime_684713 : Nat.Prime 684713 := by
  apply nodeValid_prime [2, 7, 12227] ⟨684713, 3, [(2, 3), (7, 1), (12227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_12227
  · decide +kernel

theorem prime_724733 : Nat.Prime 724733 := by
  apply nodeValid_prime [2, 181183] ⟨724733, 2, [(2, 2), (181183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_181183
  · decide +kernel

theorem prime_730571 : Nat.Prime 730571 := by
  apply nodeValid_prime [2, 5, 43, 1699] ⟨730571, 2, [(2, 1), (5, 1), (43, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_1699
  · decide +kernel

theorem prime_739847 : Nat.Prime 739847 := by
  apply nodeValid_prime [2, 31, 11933] ⟨739847, 5, [(2, 1), (31, 1), (11933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_11933
  · decide +kernel

theorem prime_885721 : Nat.Prime 885721 := by
  apply nodeValid_prime [2, 3, 5, 11, 61] ⟨885721, 23, [(2, 3), (3, 1), (5, 1), (11, 2), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_61
  · decide +kernel

theorem prime_968027 : Nat.Prime 968027 := by
  apply nodeValid_prime [2, 431, 1123] ⟨968027, 2, [(2, 1), (431, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_1123
  · decide +kernel

theorem prime_1031741 : Nat.Prime 1031741 := by
  apply nodeValid_prime [2, 5, 79, 653] ⟨1031741, 2, [(2, 2), (5, 1), (79, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_653
  · decide +kernel

theorem prime_1058567 : Nat.Prime 1058567 := by
  apply nodeValid_prime [2, 19, 89, 313] ⟨1058567, 5, [(2, 1), (19, 1), (89, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_89
    · exact prime_313
  · decide +kernel

theorem prime_1108711 : Nat.Prime 1108711 := by
  apply nodeValid_prime [2, 3, 5, 97, 127] ⟨1108711, 6, [(2, 1), (3, 2), (5, 1), (97, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_127
  · decide +kernel

theorem prime_1332343 : Nat.Prime 1332343 := by
  apply nodeValid_prime [2, 3, 11, 2243] ⟨1332343, 3, [(2, 1), (3, 3), (11, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2243
  · decide +kernel

theorem prime_1397443 : Nat.Prime 1397443 := by
  apply nodeValid_prime [2, 3, 232907] ⟨1397443, 2, [(2, 1), (3, 1), (232907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_232907
  · decide +kernel

theorem prime_1429367 : Nat.Prime 1429367 := by
  apply nodeValid_prime [2, 151, 4733] ⟨1429367, 5, [(2, 1), (151, 1), (4733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_4733
  · decide +kernel

theorem prime_1453553 : Nat.Prime 1453553 := by
  apply nodeValid_prime [2, 90847] ⟨1453553, 3, [(2, 4), (90847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_90847
  · decide +kernel

theorem prime_1485413 : Nat.Prime 1485413 := by
  apply nodeValid_prime [2, 371353] ⟨1485413, 2, [(2, 2), (371353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_371353
  · decide +kernel

theorem prime_1712231 : Nat.Prime 1712231 := by
  apply nodeValid_prime [2, 5, 13, 13171] ⟨1712231, 31, [(2, 1), (5, 1), (13, 1), (13171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_13171
  · decide +kernel

theorem prime_1783669 : Nat.Prime 1783669 := by
  apply nodeValid_prime [2, 3, 148639] ⟨1783669, 2, [(2, 2), (3, 1), (148639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_148639
  · decide +kernel

theorem prime_1803089 : Nat.Prime 1803089 := by
  apply nodeValid_prime [2, 7, 17, 947] ⟨1803089, 3, [(2, 4), (7, 1), (17, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_947
  · decide +kernel

theorem prime_1874549 : Nat.Prime 1874549 := by
  apply nodeValid_prime [2, 13, 47, 59] ⟨1874549, 2, [(2, 2), (13, 2), (47, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_59
  · decide +kernel

theorem prime_2063483 : Nat.Prime 2063483 := by
  apply nodeValid_prime [2, 1031741] ⟨2063483, 2, [(2, 1), (1031741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1031741
  · decide +kernel

theorem prime_3190981 : Nat.Prime 3190981 := by
  apply nodeValid_prime [2, 3, 5, 13, 4091] ⟨3190981, 7, [(2, 2), (3, 1), (5, 1), (13, 1), (4091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_4091
  · decide +kernel

theorem prime_3572003 : Nat.Prime 3572003 := by
  apply nodeValid_prime [2, 7, 41, 127] ⟨3572003, 2, [(2, 1), (7, 3), (41, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_127
  · decide +kernel

theorem prime_3706123 : Nat.Prime 3706123 := by
  apply nodeValid_prime [2, 3, 7, 88241] ⟨3706123, 2, [(2, 1), (3, 1), (7, 1), (88241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_88241
  · decide +kernel

theorem prime_6351403 : Nat.Prime 6351403 := by
  apply nodeValid_prime [2, 3, 1058567] ⟨6351403, 5, [(2, 1), (3, 1), (1058567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1058567
  · decide +kernel

theorem prime_7616027 : Nat.Prime 7616027 := by
  apply nodeValid_prime [2, 11, 103, 3361] ⟨7616027, 2, [(2, 1), (11, 1), (103, 1), (3361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_103
    · exact prime_3361
  · decide +kernel

theorem prime_8038819 : Nat.Prime 8038819 := by
  apply nodeValid_prime [2, 3, 148867] ⟨8038819, 2, [(2, 1), (3, 3), (148867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_148867
  · decide +kernel

theorem prime_8326603 : Nat.Prime 8326603 := by
  apply nodeValid_prime [2, 3, 462589] ⟨8326603, 2, [(2, 1), (3, 2), (462589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_462589
  · decide +kernel

theorem prime_8576203 : Nat.Prime 8576203 := by
  apply nodeValid_prime [2, 3, 1429367] ⟨8576203, 5, [(2, 1), (3, 1), (1429367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1429367
  · decide +kernel

theorem prime_8693957 : Nat.Prime 8693957 := by
  apply nodeValid_prime [2, 439, 4951] ⟨8693957, 2, [(2, 2), (439, 1), (4951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_439
    · exact prime_4951
  · decide +kernel

theorem prime_8826421 : Nat.Prime 8826421 := by
  apply nodeValid_prime [2, 3, 5, 147107] ⟨8826421, 10, [(2, 2), (3, 1), (5, 1), (147107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_147107
  · decide +kernel

theorem prime_9912599 : Nat.Prime 9912599 := by
  apply nodeValid_prime [2, 17, 291547] ⟨9912599, 7, [(2, 1), (17, 1), (291547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_291547
  · decide +kernel

theorem prime_10928543 : Nat.Prime 10928543 := by
  apply nodeValid_prime [2, 23, 37, 6421] ⟨10928543, 5, [(2, 1), (23, 1), (37, 1), (6421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_6421
  · decide +kernel

theorem prime_19236023 : Nat.Prime 19236023 := by
  apply nodeValid_prime [2, 13, 739847] ⟨19236023, 5, [(2, 1), (13, 1), (739847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_739847
  · decide +kernel

theorem prime_20349743 : Nat.Prime 20349743 := by
  apply nodeValid_prime [2, 7, 1453553] ⟨20349743, 5, [(2, 1), (7, 1), (1453553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1453553
  · decide +kernel

theorem prime_26881091 : Nat.Prime 26881091 := by
  apply nodeValid_prime [2, 5, 149, 18041] ⟨26881091, 2, [(2, 1), (5, 1), (149, 1), (18041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_149
    · exact prime_18041
  · decide +kernel

theorem prime_31344011 : Nat.Prime 31344011 := by
  apply nodeValid_prime [2, 5, 73, 42937] ⟨31344011, 2, [(2, 1), (5, 1), (73, 1), (42937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_42937
  · decide +kernel

theorem prime_33348043 : Nat.Prime 33348043 := by
  apply nodeValid_prime [2, 3, 7, 13, 20359] ⟨33348043, 2, [(2, 1), (3, 2), (7, 1), (13, 1), (20359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_20359
  · decide +kernel

theorem prime_34916381 : Nat.Prime 34916381 := by
  apply nodeValid_prime [2, 5, 67, 71, 367] ⟨34916381, 3, [(2, 2), (5, 1), (67, 1), (71, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_71
    · exact prime_367
  · decide +kernel

theorem prime_35194171 : Nat.Prime 35194171 := by
  apply nodeValid_prime [2, 3, 5, 11, 106649] ⟨35194171, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (106649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_106649
  · decide +kernel

theorem prime_38472047 : Nat.Prime 38472047 := by
  apply nodeValid_prime [2, 19236023] ⟨38472047, 5, [(2, 1), (19236023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19236023
  · decide +kernel

theorem prime_40699487 : Nat.Prime 40699487 := by
  apply nodeValid_prime [2, 20349743] ⟨40699487, 5, [(2, 1), (20349743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20349743
  · decide +kernel

theorem prime_41661329 : Nat.Prime 41661329 := by
  apply nodeValid_prime [2, 541, 4813] ⟨41661329, 3, [(2, 4), (541, 1), (4813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_541
    · exact prime_4813
  · decide +kernel

theorem prime_56222069 : Nat.Prime 56222069 := by
  apply nodeValid_prime [2, 7, 29, 69239] ⟨56222069, 2, [(2, 2), (7, 1), (29, 1), (69239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_69239
  · decide +kernel

theorem prime_76872277 : Nat.Prime 76872277 := by
  apply nodeValid_prime [2, 3, 13, 83, 1979] ⟨76872277, 2, [(2, 2), (3, 2), (13, 1), (83, 1), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_83
    · exact prime_1979
  · decide +kernel

theorem prime_78037723 : Nat.Prime 78037723 := by
  apply nodeValid_prime [2, 3, 7, 431, 479] ⟨78037723, 2, [(2, 1), (3, 3), (7, 1), (431, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_431
    · exact prime_479
  · decide +kernel

theorem prime_95724199 : Nat.Prime 95724199 := by
  apply nodeValid_prime [2, 3, 1997, 2663] ⟨95724199, 3, [(2, 1), (3, 2), (1997, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1997
    · exact prime_2663
  · decide +kernel

theorem prime_114685861 : Nat.Prime 114685861 := by
  apply nodeValid_prime [2, 3, 5, 467, 4093] ⟨114685861, 2, [(2, 2), (3, 1), (5, 1), (467, 1), (4093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_467
    · exact prime_4093
  · decide +kernel

theorem prime_147746719 : Nat.Prime 147746719 := by
  apply nodeValid_prime [2, 3, 7, 757, 1549] ⟨147746719, 6, [(2, 1), (3, 2), (7, 1), (757, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_757
    · exact prime_1549
  · decide +kernel

theorem prime_174629071 : Nat.Prime 174629071 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 113, 223] ⟨174629071, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (113, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_113
    · exact prime_223
  · decide +kernel

theorem prime_209498287 : Nat.Prime 209498287 := by
  apply nodeValid_prime [2, 3, 34916381] ⟨209498287, 6, [(2, 1), (3, 1), (34916381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_34916381
  · decide +kernel

theorem prime_237946087 : Nat.Prime 237946087 := by
  apply nodeValid_prime [2, 3, 7, 23, 3041] ⟨237946087, 3, [(2, 1), (3, 5), (7, 1), (23, 1), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_3041
  · decide +kernel

theorem prime_292926937 : Nat.Prime 292926937 := by
  apply nodeValid_prime [2, 3, 31, 47, 8377] ⟨292926937, 10, [(2, 3), (3, 1), (31, 1), (47, 1), (8377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_47
    · exact prime_8377
  · decide +kernel

theorem prime_343700411 : Nat.Prime 343700411 := by
  apply nodeValid_prime [2, 5, 31, 1108711] ⟨343700411, 2, [(2, 1), (5, 1), (31, 1), (1108711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1108711
  · decide +kernel

theorem prime_582862211 : Nat.Prime 582862211 := by
  apply nodeValid_prime [2, 5, 7, 8326603] ⟨582862211, 2, [(2, 1), (5, 1), (7, 1), (8326603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_8326603
  · decide +kernel

theorem prime_618983269 : Nat.Prime 618983269 := by
  apply nodeValid_prime [2, 3, 23, 127, 17659] ⟨618983269, 2, [(2, 2), (3, 1), (23, 1), (127, 1), (17659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_127
    · exact prime_17659
  · decide +kernel

theorem prime_630033601 : Nat.Prime 630033601 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 1103] ⟨630033601, 26, [(2, 6), (3, 1), (5, 2), (7, 1), (17, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_1103
  · decide +kernel

theorem prime_687400823 : Nat.Prime 687400823 := by
  apply nodeValid_prime [2, 343700411] ⟨687400823, 5, [(2, 1), (343700411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_343700411
  · decide +kernel

theorem prime_859314977 : Nat.Prime 859314977 := by
  apply nodeValid_prime [2, 13, 19, 8363] ⟨859314977, 3, [(2, 5), (13, 2), (19, 1), (8363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_8363
  · decide +kernel

theorem prime_1861517197 : Nat.Prime 1861517197 := by
  apply nodeValid_prime [2, 3, 7, 11, 149, 4507] ⟨1861517197, 2, [(2, 2), (3, 2), (7, 1), (11, 1), (149, 1), (4507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_149
    · exact prime_4507
  · decide +kernel

theorem prime_2852796241 : Nat.Prime 2852796241 := by
  apply nodeValid_prime [2, 3, 5, 7, 188677] ⟨2852796241, 17, [(2, 4), (3, 3), (5, 1), (7, 1), (188677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_188677
  · decide +kernel

theorem prime_3965526997 : Nat.Prime 3965526997 := by
  apply nodeValid_prime [2, 3, 193, 1712231] ⟨3965526997, 2, [(2, 2), (3, 1), (193, 1), (1712231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_1712231
  · decide +kernel

theorem prime_4178120899 : Nat.Prime 4178120899 := by
  apply nodeValid_prime [2, 3, 7, 83, 397, 3019] ⟨4178120899, 2, [(2, 1), (3, 1), (7, 1), (83, 1), (397, 1), (3019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_83
    · exact prime_397
    · exact prime_3019
  · decide +kernel

theorem prime_4626922451 : Nat.Prime 4626922451 := by
  apply nodeValid_prime [2, 5, 29, 3190981] ⟨4626922451, 2, [(2, 1), (5, 2), (29, 1), (3190981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3190981
  · decide +kernel

theorem prime_6268802201 : Nat.Prime 6268802201 := by
  apply nodeValid_prime [2, 5, 31344011] ⟨6268802201, 3, [(2, 3), (5, 2), (31344011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31344011
  · decide +kernel

theorem prime_6501662423 : Nat.Prime 6501662423 := by
  apply nodeValid_prime [2, 37, 401, 219103] ⟨6501662423, 5, [(2, 1), (37, 1), (401, 1), (219103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_401
    · exact prime_219103
  · decide +kernel

theorem prime_7772506519 : Nat.Prime 7772506519 := by
  apply nodeValid_prime [2, 3, 7, 23, 293, 3923] ⟨7772506519, 3, [(2, 1), (3, 1), (7, 2), (23, 1), (293, 1), (3923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_293
    · exact prime_3923
  · decide +kernel

theorem prime_8647710371 : Nat.Prime 8647710371 := by
  apply nodeValid_prime [2, 5, 13, 281, 236729] ⟨8647710371, 6, [(2, 1), (5, 1), (13, 1), (281, 1), (236729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_281
    · exact prime_236729
  · decide +kernel

theorem prime_9852049463 : Nat.Prime 9852049463 := by
  apply nodeValid_prime [2, 223, 4603, 4799] ⟨9852049463, 5, [(2, 1), (223, 1), (4603, 1), (4799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_4603
    · exact prime_4799
  · decide +kernel

theorem prime_10651725181 : Nat.Prime 10651725181 := by
  apply nodeValid_prime [2, 3, 5, 730571] ⟨10651725181, 2, [(2, 2), (3, 6), (5, 1), (730571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_730571
  · decide +kernel

theorem prime_15314608031 : Nat.Prime 15314608031 := by
  apply nodeValid_prime [2, 5, 1031, 1485413] ⟨15314608031, 14, [(2, 1), (5, 1), (1031, 1), (1485413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1031
    · exact prime_1485413
  · decide +kernel

theorem prime_18517831259 : Nat.Prime 18517831259 := by
  apply nodeValid_prime [2, 1049, 8826421] ⟨18517831259, 2, [(2, 1), (1049, 1), (8826421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1049
    · exact prime_8826421
  · decide +kernel

theorem prime_27761534707 : Nat.Prime 27761534707 := by
  apply nodeValid_prime [2, 3, 4626922451] ⟨27761534707, 2, [(2, 1), (3, 1), (4626922451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4626922451
  · decide +kernel

theorem prime_34264236529 : Nat.Prime 34264236529 := by
  apply nodeValid_prime [2, 3, 237946087] ⟨34264236529, 7, [(2, 4), (3, 2), (237946087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_237946087
  · decide +kernel

theorem prime_38468905927 : Nat.Prime 38468905927 := by
  apply nodeValid_prime [2, 3, 11, 582862211] ⟨38468905927, 3, [(2, 1), (3, 1), (11, 1), (582862211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_582862211
  · decide +kernel

theorem prime_42459837803 : Nat.Prime 42459837803 := by
  apply nodeValid_prime [2, 29, 317, 79633] ⟨42459837803, 2, [(2, 1), (29, 2), (317, 1), (79633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_317
    · exact prime_79633
  · decide +kernel

theorem prime_67641080747 : Nat.Prime 67641080747 := by
  apply nodeValid_prime [2, 18757, 1803089] ⟨67641080747, 2, [(2, 1), (18757, 1), (1803089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_18757
    · exact prime_1803089
  · decide +kernel

theorem prime_130971803251 : Nat.Prime 130971803251 := by
  apply nodeValid_prime [2, 3, 5, 174629071] ⟨130971803251, 11, [(2, 1), (3, 1), (5, 3), (174629071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_174629071
  · decide +kernel

theorem prime_181847738173 : Nat.Prime 181847738173 := by
  apply nodeValid_prime [2, 3, 19, 13513, 59023] ⟨181847738173, 5, [(2, 2), (3, 1), (19, 1), (13513, 1), (59023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_13513
    · exact prime_59023
  · decide +kernel

theorem prime_188369678803 : Nat.Prime 188369678803 := by
  apply nodeValid_prime [2, 3, 173, 4129, 43951] ⟨188369678803, 3, [(2, 1), (3, 1), (173, 1), (4129, 1), (43951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_4129
    · exact prime_43951
  · decide +kernel

theorem prime_201533732657 : Nat.Prime 201533732657 := by
  apply nodeValid_prime [2, 43, 292926937] ⟨201533732657, 3, [(2, 4), (43, 1), (292926937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_292926937
  · decide +kernel

theorem prime_948259781129 : Nat.Prime 948259781129 := by
  apply nodeValid_prime [2, 11, 23, 47, 227, 43913] ⟨948259781129, 3, [(2, 3), (11, 1), (23, 1), (47, 1), (227, 1), (43913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_47
    · exact prime_227
    · exact prime_43913
  · decide +kernel

theorem prime_948902512301 : Nat.Prime 948902512301 := by
  apply nodeValid_prime [2, 5, 353, 26881091] ⟨948902512301, 2, [(2, 2), (5, 2), (353, 1), (26881091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_353
    · exact prime_26881091
  · decide +kernel

theorem prime_1888818788419 : Nat.Prime 1888818788419 := by
  apply nodeValid_prime [2, 3, 17, 18517831259] ⟨1888818788419, 10, [(2, 1), (3, 1), (17, 1), (18517831259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_18517831259
  · decide +kernel

theorem prime_1900377844639 : Nat.Prime 1900377844639 := by
  apply nodeValid_prime [2, 3, 7, 13, 61, 2267, 25169] ⟨1900377844639, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (61, 1), (2267, 1), (25169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_2267
    · exact prime_25169
  · decide +kernel

theorem prime_1908110397997 : Nat.Prime 1908110397997 := by
  apply nodeValid_prime [2, 3, 11, 23, 209498287] ⟨1908110397997, 2, [(2, 2), (3, 2), (11, 1), (23, 1), (209498287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_209498287
  · decide +kernel

theorem prime_3787900521833 : Nat.Prime 3787900521833 := by
  apply nodeValid_prime [2, 7, 67641080747] ⟨3787900521833, 3, [(2, 3), (7, 1), (67641080747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67641080747
  · decide +kernel

theorem prime_7534787151253 : Nat.Prime 7534787151253 := by
  apply nodeValid_prime [2, 3, 41, 15314608031] ⟨7534787151253, 2, [(2, 2), (3, 1), (41, 1), (15314608031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_15314608031
  · decide +kernel

theorem prime_7534787152121 : Nat.Prime 7534787152121 := by
  apply nodeValid_prime [2, 5, 188369678803] ⟨7534787152121, 3, [(2, 3), (5, 1), (188369678803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_188369678803
  · decide +kernel

theorem prime_7534787175563 : Nat.Prime 7534787175563 := by
  apply nodeValid_prime [2, 43, 593, 147746719] ⟨7534787175563, 2, [(2, 1), (43, 1), (593, 1), (147746719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_593
    · exact prime_147746719
  · decide +kernel

theorem prime_7539905561693 : Nat.Prime 7539905561693 := by
  apply nodeValid_prime [2, 7, 38468905927] ⟨7539905561693, 2, [(2, 2), (7, 2), (38468905927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_38468905927
  · decide +kernel

theorem prime_7539905562647 : Nat.Prime 7539905562647 := by
  apply nodeValid_prime [2, 211, 439, 40699487] ⟨7539905562647, 5, [(2, 1), (211, 1), (439, 1), (40699487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_439
    · exact prime_40699487
  · decide +kernel

theorem prime_7539905659249 : Nat.Prime 7539905659249 := by
  apply nodeValid_prime [2, 3, 1361, 38472047] ⟨7539905659249, 7, [(2, 4), (3, 2), (1361, 1), (38472047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1361
    · exact prime_38472047
  · decide +kernel

theorem prime_7545026461781 : Nat.Prime 7545026461781 := by
  apply nodeValid_prime [2, 5, 31, 179, 829, 82009] ⟨7545026461781, 2, [(2, 2), (5, 1), (31, 1), (179, 1), (829, 1), (82009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_179
    · exact prime_829
    · exact prime_82009
  · decide +kernel

theorem prime_7545026464103 : Nat.Prime 7545026464103 := by
  apply nodeValid_prime [2, 23, 421, 569, 684713] ⟨7545026464103, 5, [(2, 1), (23, 1), (421, 1), (569, 1), (684713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_421
    · exact prime_569
    · exact prime_684713
  · decide +kernel

theorem prime_7545026504107 : Nat.Prime 7545026504107 := by
  apply nodeValid_prime [2, 3, 7, 13, 191, 8038819] ⟨7545026504107, 2, [(2, 1), (3, 3), (7, 1), (13, 1), (191, 1), (8038819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_191
    · exact prime_8038819
  · decide +kernel

theorem prime_7550149585217 : Nat.Prime 7550149585217 := by
  apply nodeValid_prime [2, 7, 211, 2879, 27743] ⟨7550149585217, 3, [(2, 6), (7, 1), (211, 1), (2879, 1), (27743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_211
    · exact prime_2879
    · exact prime_27743
  · decide +kernel

theorem prime_7550149587509 : Nat.Prime 7550149587509 := by
  apply nodeValid_prime [2, 11, 17, 5659, 1783669] ⟨7550149587509, 2, [(2, 2), (11, 1), (17, 1), (5659, 1), (1783669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_5659
    · exact prime_1783669
  · decide +kernel

theorem prime_7550149700251 : Nat.Prime 7550149700251 := by
  apply nodeValid_prime [2, 3, 5, 43, 78037723] ⟨7550149700251, 10, [(2, 1), (3, 2), (5, 3), (43, 1), (78037723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_78037723
  · decide +kernel

theorem prime_7555275150959 : Nat.Prime 7555275150959 := by
  apply nodeValid_prime [2, 32939, 114685861] ⟨7555275150959, 7, [(2, 1), (32939, 1), (114685861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32939
    · exact prime_114685861
  · decide +kernel

theorem prime_7555275153677 : Nat.Prime 7555275153677 := by
  apply nodeValid_prime [2, 1888818788419] ⟨7555275153677, 2, [(2, 2), (1888818788419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1888818788419
  · decide +kernel

theorem prime_7555275249941 : Nat.Prime 7555275249941 := by
  apply nodeValid_prime [2, 5, 11, 43, 3691, 216379] ⟨7555275249941, 7, [(2, 2), (5, 1), (11, 1), (43, 1), (3691, 1), (216379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_3691
    · exact prime_216379
  · decide +kernel

theorem prime_7560403161133 : Nat.Prime 7560403161133 := by
  apply nodeValid_prime [2, 3, 251, 2593, 968027] ⟨7560403161133, 15, [(2, 2), (3, 1), (251, 1), (2593, 1), (968027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_2593
    · exact prime_968027
  · decide +kernel

theorem prime_7560403211869 : Nat.Prime 7560403211869 := by
  apply nodeValid_prime [2, 3, 13, 5651, 8576203] ⟨7560403211869, 6, [(2, 2), (3, 1), (13, 1), (5651, 1), (8576203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_5651
    · exact prime_8576203
  · decide +kernel

theorem prime_7560403212001 : Nat.Prime 7560403212001 := by
  apply nodeValid_prime [2, 3, 5, 630033601] ⟨7560403212001, 7, [(2, 5), (3, 1), (5, 3), (630033601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_630033601
  · decide +kernel

theorem prime_7565533436371 : Nat.Prime 7565533436371 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 17, 79, 2063483] ⟨7565533436371, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (79, 1), (2063483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_79
    · exact prime_2063483
  · decide +kernel

theorem prime_7565533457939 : Nat.Prime 7565533457939 := by
  apply nodeValid_prime [2, 5503, 687400823] ⟨7565533457939, 2, [(2, 1), (5503, 1), (687400823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5503
    · exact prime_687400823
  · decide +kernel

theorem prime_7565533459177 : Nat.Prime 7565533459177 := by
  apply nodeValid_prime [2, 3, 7, 11, 59, 9912599] ⟨7565533459177, 5, [(2, 3), (3, 1), (7, 2), (11, 1), (59, 1), (9912599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_59
    · exact prime_9912599
  · decide +kernel

theorem prime_7570665943189 : Nat.Prime 7570665943189 := by
  apply nodeValid_prime [2, 3, 82837, 7616027] ⟨7570665943189, 2, [(2, 2), (3, 1), (82837, 1), (7616027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_82837
    · exact prime_7616027
  · decide +kernel

theorem prime_7570665943769 : Nat.Prime 7570665943769 := by
  apply nodeValid_prime [2, 53, 83, 163, 15901] ⟨7570665943769, 3, [(2, 3), (53, 1), (83, 2), (163, 1), (15901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_83
    · exact prime_163
    · exact prime_15901
  · decide +kernel

theorem prime_7570666064341 : Nat.Prime 7570666064341 := by
  apply nodeValid_prime [2, 3, 5, 277, 1874549] ⟨7570666064341, 6, [(2, 2), (3, 6), (5, 1), (277, 1), (1874549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_277
    · exact prime_1874549
  · decide +kernel

theorem prime_7575801043667 : Nat.Prime 7575801043667 := by
  apply nodeValid_prime [2, 3787900521833] ⟨7575801043667, 2, [(2, 1), (3787900521833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3787900521833
  · decide +kernel

theorem prime_7575801064729 : Nat.Prime 7575801064729 := by
  apply nodeValid_prime [2, 3, 13, 3823, 6351403] ⟨7575801064729, 22, [(2, 3), (3, 1), (13, 1), (3823, 1), (6351403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3823
    · exact prime_6351403
  · decide +kernel

theorem prime_7575801066517 : Nat.Prime 7575801066517 := by
  apply nodeValid_prime [2, 3, 223, 5279, 536279] ⟨7575801066517, 5, [(2, 2), (3, 1), (223, 1), (5279, 1), (536279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_5279
    · exact prime_536279
  · decide +kernel

theorem prime_7580938385219 : Nat.Prime 7580938385219 := by
  apply nodeValid_prime [2, 11, 53, 6501662423] ⟨7580938385219, 6, [(2, 1), (11, 1), (53, 1), (6501662423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_53
    · exact prime_6501662423
  · decide +kernel

theorem prime_7580938405577 : Nat.Prime 7580938405577 := by
  apply nodeValid_prime [2, 271, 22063, 158489] ⟨7580938405577, 3, [(2, 3), (271, 1), (22063, 1), (158489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_22063
    · exact prime_158489
  · decide +kernel

theorem prime_7580938405991 : Nat.Prime 7580938405991 := by
  apply nodeValid_prime [2, 5, 19, 29947, 1332343] ⟨7580938405991, 13, [(2, 1), (5, 1), (19, 1), (29947, 1), (1332343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_29947
    · exact prime_1332343
  · decide +kernel

theorem prime_7586078086511 : Nat.Prime 7586078086511 := by
  apply nodeValid_prime [2, 5, 7, 11, 9852049463] ⟨7586078086511, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (9852049463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_9852049463
  · decide +kernel

theorem prime_7586078248963 : Nat.Prime 7586078248963 := by
  apply nodeValid_prime [2, 3, 89, 26297, 180073] ⟨7586078248963, 2, [(2, 1), (3, 2), (89, 1), (26297, 1), (180073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_26297
    · exact prime_180073
  · decide +kernel

theorem prime_7586078249033 : Nat.Prime 7586078249033 := by
  apply nodeValid_prime [2, 948259781129] ⟨7586078249033, 3, [(2, 3), (948259781129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_948259781129
  · decide +kernel

theorem prime_7591220098409 : Nat.Prime 7591220098409 := by
  apply nodeValid_prime [2, 948902512301] ⟨7591220098409, 3, [(2, 3), (948902512301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_948902512301
  · decide +kernel

theorem prime_7591220156899 : Nat.Prime 7591220156899 := by
  apply nodeValid_prime [2, 3, 7, 59, 1409, 724733] ⟨7591220156899, 2, [(2, 1), (3, 2), (7, 1), (59, 1), (1409, 1), (724733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_1409
    · exact prime_724733
  · decide +kernel

theorem prime_7596364588559 : Nat.Prime 7596364588559 := by
  apply nodeValid_prime [2, 29, 130971803251] ⟨7596364588559, 13, [(2, 1), (29, 1), (130971803251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_130971803251
  · decide +kernel

theorem prime_7596364668043 : Nat.Prime 7596364668043 := by
  apply nodeValid_prime [2, 3, 115849, 10928543] ⟨7596364668043, 2, [(2, 1), (3, 1), (115849, 1), (10928543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_115849
    · exact prime_10928543
  · decide +kernel

theorem prime_7596364668587 : Nat.Prime 7596364668587 := by
  apply nodeValid_prime [2, 49409, 76872277] ⟨7596364668587, 2, [(2, 1), (49409, 1), (76872277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_49409
    · exact prime_76872277
  · decide +kernel

theorem prime_7601511375583 : Nat.Prime 7601511375583 := by
  apply nodeValid_prime [2, 3, 163, 7772506519] ⟨7601511375583, 3, [(2, 1), (3, 1), (163, 1), (7772506519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_7772506519
  · decide +kernel

theorem prime_7601511378557 : Nat.Prime 7601511378557 := by
  apply nodeValid_prime [2, 1900377844639] ⟨7601511378557, 2, [(2, 2), (1900377844639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1900377844639
  · decide +kernel

theorem prime_7601511378599 : Nat.Prime 7601511378599 := by
  apply nodeValid_prime [2, 19, 43, 3329, 1397443] ⟨7601511378599, 13, [(2, 1), (19, 1), (43, 1), (3329, 1), (1397443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_3329
    · exact prime_1397443
  · decide +kernel

theorem prime_7606660509439 : Nat.Prime 7606660509439 := by
  apply nodeValid_prime [2, 3, 37, 34264236529] ⟨7606660509439, 6, [(2, 1), (3, 1), (37, 1), (34264236529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_34264236529
  · decide +kernel

theorem prime_7606660509719 : Nat.Prime 7606660509719 := by
  apply nodeValid_prime [2, 137, 27761534707] ⟨7606660509719, 13, [(2, 1), (137, 1), (27761534707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_27761534707
  · decide +kernel

theorem prime_7606660520101 : Nat.Prime 7606660520101 := by
  apply nodeValid_prime [2, 3, 5, 28627, 885721] ⟨7606660520101, 18, [(2, 2), (3, 1), (5, 2), (28627, 1), (885721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_28627
    · exact prime_885721
  · decide +kernel

theorem prime_7611812033431 : Nat.Prime 7611812033431 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 14699, 82591] ⟨7611812033431, 7, [(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (14699, 1), (82591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_14699
    · exact prime_82591
  · decide +kernel

theorem prime_7611812066267 : Nat.Prime 7611812066267 := by
  apply nodeValid_prime [2, 43, 103, 859314977] ⟨7611812066267, 2, [(2, 1), (43, 1), (103, 1), (859314977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_103
    · exact prime_859314977
  · decide +kernel

theorem prime_7611812067437 : Nat.Prime 7611812067437 := by
  apply nodeValid_prime [2, 31, 53, 3257, 355609] ⟨7611812067437, 2, [(2, 2), (31, 1), (53, 1), (3257, 1), (355609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_53
    · exact prime_3257
    · exact prime_355609
  · decide +kernel

theorem prime_7616965908121 : Nat.Prime 7616965908121 := by
  apply nodeValid_prime [2, 3, 5, 1129, 56222069] ⟨7616965908121, 14, [(2, 3), (3, 1), (5, 1), (1129, 1), (56222069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1129
    · exact prime_56222069
  · decide +kernel

theorem prime_7616965962829 : Nat.Prime 7616965962829 := by
  apply nodeValid_prime [2, 3, 19, 349, 95724199] ⟨7616965962829, 2, [(2, 2), (3, 1), (19, 1), (349, 1), (95724199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_349
    · exact prime_95724199
  · decide +kernel

theorem prime_7616965963471 : Nat.Prime 7616965963471 := by
  apply nodeValid_prime [2, 3, 5, 89, 2852796241] ⟨7616965963471, 3, [(2, 1), (3, 1), (5, 1), (89, 1), (2852796241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_2852796241
  · decide +kernel

theorem prime_7622122145041 : Nat.Prime 7622122145041 := by
  apply nodeValid_prime [2, 3, 5, 13, 281, 683, 4243] ⟨7622122145041, 11, [(2, 4), (3, 2), (5, 1), (13, 1), (281, 1), (683, 1), (4243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_281
    · exact prime_683
    · exact prime_4243
  · decide +kernel

theorem prime_7622122145173 : Nat.Prime 7622122145173 := by
  apply nodeValid_prime [2, 3, 61, 55901, 186271] ⟨7622122145173, 2, [(2, 2), (3, 1), (61, 1), (55901, 1), (186271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_55901
    · exact prime_186271
  · decide +kernel

theorem prime_7622122146071 : Nat.Prime 7622122146071 := by
  apply nodeValid_prime [2, 5, 479, 7109, 223837] ⟨7622122146071, 22, [(2, 1), (5, 1), (479, 1), (7109, 1), (223837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479
    · exact prime_7109
    · exact prime_223837
  · decide +kernel

theorem prime_7627280547121 : Nat.Prime 7627280547121 := by
  apply nodeValid_prime [2, 3, 5, 13, 10657, 229393] ⟨7627280547121, 19, [(2, 4), (3, 1), (5, 1), (13, 1), (10657, 1), (229393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_10657
    · exact prime_229393
  · decide +kernel

theorem prime_7627280547223 : Nat.Prime 7627280547223 := by
  apply nodeValid_prime [2, 3, 7, 8647710371] ⟨7627280547223, 6, [(2, 1), (3, 2), (7, 2), (8647710371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8647710371
  · decide +kernel

theorem prime_7627280739121 : Nat.Prime 7627280739121 := by
  apply nodeValid_prime [2, 3, 5, 7, 43, 35194171] ⟨7627280739121, 19, [(2, 4), (3, 2), (5, 1), (7, 1), (43, 1), (35194171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_35194171
  · decide +kernel

theorem prime_7632441591923 : Nat.Prime 7632441591923 := by
  apply nodeValid_prime [2, 7, 17, 509, 3706123] ⟨7632441591923, 2, [(2, 1), (7, 1), (17, 2), (509, 1), (3706123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_509
    · exact prime_3706123
  · decide +kernel

theorem prime_7632441591989 : Nat.Prime 7632441591989 := by
  apply nodeValid_prime [2, 1908110397997] ⟨7632441591989, 2, [(2, 2), (1908110397997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1908110397997
  · decide +kernel

theorem prime_7632441690221 : Nat.Prime 7632441690221 := by
  apply nodeValid_prime [2, 5, 19, 5623, 3572003] ⟨7632441690221, 2, [(2, 2), (5, 1), (19, 1), (5623, 1), (3572003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_5623
    · exact prime_3572003
  · decide +kernel

theorem prime_7637604996223 : Nat.Prime 7637604996223 := by
  apply nodeValid_prime [2, 3, 107, 3965526997] ⟨7637604996223, 3, [(2, 1), (3, 2), (107, 1), (3965526997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_3965526997
  · decide +kernel

theorem prime_7637605003267 : Nat.Prime 7637605003267 := by
  apply nodeValid_prime [2, 3, 7, 181847738173] ⟨7637605003267, 2, [(2, 1), (3, 1), (7, 1), (181847738173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_181847738173
  · decide +kernel

theorem prime_7637605003373 : Nat.Prime 7637605003373 := by
  apply nodeValid_prime [2, 457, 4178120899] ⟨7637605003373, 2, [(2, 2), (457, 1), (4178120899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_4178120899
  · decide +kernel

theorem prime_7642770659131 : Nat.Prime 7642770659131 := by
  apply nodeValid_prime [2, 3, 5, 29303, 8693957] ⟨7642770659131, 3, [(2, 1), (3, 1), (5, 1), (29303, 1), (8693957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29303
    · exact prime_8693957
  · decide +kernel

theorem prime_7642770804541 : Nat.Prime 7642770804541 := by
  apply nodeValid_prime [2, 3, 5, 42459837803] ⟨7642770804541, 2, [(2, 2), (3, 2), (5, 1), (42459837803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_42459837803
  · decide +kernel

theorem prime_7642770805051 : Nat.Prime 7642770805051 := by
  apply nodeValid_prime [2, 3, 5, 1223, 41661329] ⟨7642770805051, 2, [(2, 1), (3, 1), (5, 2), (1223, 1), (41661329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1223
    · exact prime_41661329
  · decide +kernel

theorem prime_7647938679959 : Nat.Prime 7647938679959 := by
  apply nodeValid_prime [2, 359, 10651725181] ⟨7647938679959, 7, [(2, 1), (359, 1), (10651725181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_10651725181
  · decide +kernel

theorem prime_7647938680177 : Nat.Prime 7647938680177 := by
  apply nodeValid_prime [2, 3, 139, 13147, 29063] ⟨7647938680177, 5, [(2, 4), (3, 2), (139, 1), (13147, 1), (29063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_13147
    · exact prime_29063
  · decide +kernel

theorem prime_7647938685221 : Nat.Prime 7647938685221 := by
  apply nodeValid_prime [2, 5, 61, 6268802201] ⟨7647938685221, 3, [(2, 2), (5, 1), (61, 1), (6268802201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_6268802201
  · decide +kernel

theorem prime_7653109084157 : Nat.Prime 7653109084157 := by
  apply nodeValid_prime [2, 57373, 33348043] ⟨7653109084157, 2, [(2, 2), (57373, 1), (33348043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_57373
    · exact prime_33348043
  · decide +kernel

theorem prime_7653109137917 : Nat.Prime 7653109137917 := by
  apply nodeValid_prime [2, 11, 281, 618983269] ⟨7653109137917, 2, [(2, 2), (11, 1), (281, 1), (618983269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_281
    · exact prime_618983269
  · decide +kernel

theorem prime_7653109140503 : Nat.Prime 7653109140503 := by
  apply nodeValid_prime [2, 7, 23, 61, 181, 1153, 1867] ⟨7653109140503, 5, [(2, 1), (7, 1), (23, 1), (61, 1), (181, 1), (1153, 1), (1867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_61
    · exact prime_181
    · exact prime_1153
    · exact prime_1867
  · decide +kernel

theorem prime_7658281747241 : Nat.Prime 7658281747241 := by
  apply nodeValid_prime [2, 5, 2741, 2749, 25409] ⟨7658281747241, 6, [(2, 3), (5, 1), (2741, 1), (2749, 1), (25409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2741
    · exact prime_2749
    · exact prime_25409
  · decide +kernel

theorem prime_7658281748459 : Nat.Prime 7658281748459 := by
  apply nodeValid_prime [2, 11, 17, 1861517197] ⟨7658281748459, 2, [(2, 1), (11, 2), (17, 1), (1861517197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_1861517197
  · decide +kernel

theorem prime_7658281840967 : Nat.Prime 7658281840967 := by
  apply nodeValid_prime [2, 19, 201533732657] ⟨7658281840967, 5, [(2, 1), (19, 1), (201533732657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_201533732657
  · decide +kernel

end Sude.Lucas.Generated
