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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0094

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5987 : Nat.Prime 5987 := by
  apply nodeValid_prime [2, 41, 73] ⟨5987, 2, [(2, 1), (41, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_73
  · decide +kernel

theorem prime_10159 : Nat.Prime 10159 := by
  apply nodeValid_prime [2, 3, 1693] ⟨10159, 3, [(2, 1), (3, 1), (1693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1693
  · decide +kernel

theorem prime_11731 : Nat.Prime 11731 := by
  apply nodeValid_prime [2, 3, 5, 17, 23] ⟨11731, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_11923 : Nat.Prime 11923 := by
  apply nodeValid_prime [2, 3, 1987] ⟨11923, 5, [(2, 1), (3, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1987
  · decide +kernel

theorem prime_13259 : Nat.Prime 13259 := by
  apply nodeValid_prime [2, 7, 947] ⟨13259, 6, [(2, 1), (7, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_947
  · decide +kernel

theorem prime_13411 : Nat.Prime 13411 := by
  apply nodeValid_prime [2, 3, 5, 149] ⟨13411, 2, [(2, 1), (3, 2), (5, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_149
  · decide +kernel

theorem prime_14759 : Nat.Prime 14759 := by
  apply nodeValid_prime [2, 47, 157] ⟨14759, 17, [(2, 1), (47, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_157
  · decide +kernel

theorem prime_22861 : Nat.Prime 22861 := by
  apply nodeValid_prime [2, 3, 5, 127] ⟨22861, 2, [(2, 2), (3, 2), (5, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_127
  · decide +kernel

theorem prime_24247 : Nat.Prime 24247 := by
  apply nodeValid_prime [2, 3, 449] ⟨24247, 3, [(2, 1), (3, 3), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_449
  · decide +kernel

theorem prime_27073 : Nat.Prime 27073 := by
  apply nodeValid_prime [2, 3, 47] ⟨27073, 5, [(2, 6), (3, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_28229 : Nat.Prime 28229 := by
  apply nodeValid_prime [2, 7057] ⟨28229, 2, [(2, 2), (7057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7057
  · decide +kernel

theorem prime_30937 : Nat.Prime 30937 := by
  apply nodeValid_prime [2, 3, 1289] ⟨30937, 15, [(2, 3), (3, 1), (1289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1289
  · decide +kernel

theorem prime_30971 : Nat.Prime 30971 := by
  apply nodeValid_prime [2, 5, 19, 163] ⟨30971, 2, [(2, 1), (5, 1), (19, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_163
  · decide +kernel

theorem prime_31567 : Nat.Prime 31567 := by
  apply nodeValid_prime [2, 3, 5261] ⟨31567, 6, [(2, 1), (3, 1), (5261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5261
  · decide +kernel

theorem prime_35923 : Nat.Prime 35923 := by
  apply nodeValid_prime [2, 3, 5987] ⟨35923, 2, [(2, 1), (3, 1), (5987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5987
  · decide +kernel

theorem prime_35983 : Nat.Prime 35983 := by
  apply nodeValid_prime [2, 3, 1999] ⟨35983, 3, [(2, 1), (3, 2), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1999
  · decide +kernel

theorem prime_40949 : Nat.Prime 40949 := by
  apply nodeValid_prime [2, 29, 353] ⟨40949, 2, [(2, 2), (29, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_353
  · decide +kernel

theorem prime_41351 : Nat.Prime 41351 := by
  apply nodeValid_prime [2, 5, 827] ⟨41351, 7, [(2, 1), (5, 2), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_827
  · decide +kernel

theorem prime_42197 : Nat.Prime 42197 := by
  apply nodeValid_prime [2, 7, 11, 137] ⟨42197, 2, [(2, 2), (7, 1), (11, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_137
  · decide +kernel

theorem prime_43051 : Nat.Prime 43051 := by
  apply nodeValid_prime [2, 3, 5, 7, 41] ⟨43051, 2, [(2, 1), (3, 1), (5, 2), (7, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_46831 : Nat.Prime 46831 := by
  apply nodeValid_prime [2, 3, 5, 7, 223] ⟨46831, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_223
  · decide +kernel

theorem prime_50513 : Nat.Prime 50513 := by
  apply nodeValid_prime [2, 7, 11, 41] ⟨50513, 3, [(2, 4), (7, 1), (11, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_41
  · decide +kernel

theorem prime_53411 : Nat.Prime 53411 := by
  apply nodeValid_prime [2, 5, 7, 109] ⟨53411, 2, [(2, 1), (5, 1), (7, 2), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_109
  · decide +kernel

theorem prime_61121 : Nat.Prime 61121 := by
  apply nodeValid_prime [2, 5, 191] ⟨61121, 3, [(2, 6), (5, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_61291 : Nat.Prime 61291 := by
  apply nodeValid_prime [2, 3, 5, 227] ⟨61291, 3, [(2, 1), (3, 3), (5, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_227
  · decide +kernel

theorem prime_63211 : Nat.Prime 63211 := by
  apply nodeValid_prime [2, 3, 5, 7, 43] ⟨63211, 7, [(2, 1), (3, 1), (5, 1), (7, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_64853 : Nat.Prime 64853 := by
  apply nodeValid_prime [2, 31, 523] ⟨64853, 2, [(2, 2), (31, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_523
  · decide +kernel

theorem prime_77849 : Nat.Prime 77849 := by
  apply nodeValid_prime [2, 37, 263] ⟨77849, 3, [(2, 3), (37, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_263
  · decide +kernel

theorem prime_92951 : Nat.Prime 92951 := by
  apply nodeValid_prime [2, 5, 11, 13] ⟨92951, 11, [(2, 1), (5, 2), (11, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_96989 : Nat.Prime 96989 := by
  apply nodeValid_prime [2, 24247] ⟨96989, 2, [(2, 2), (24247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_24247
  · decide +kernel

theorem prime_108293 : Nat.Prime 108293 := by
  apply nodeValid_prime [2, 27073] ⟨108293, 2, [(2, 2), (27073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_27073
  · decide +kernel

theorem prime_109201 : Nat.Prime 109201 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨109201, 17, [(2, 4), (3, 1), (5, 2), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_110023 : Nat.Prime 110023 := by
  apply nodeValid_prime [2, 3, 11, 1667] ⟨110023, 6, [(2, 1), (3, 1), (11, 1), (1667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1667
  · decide +kernel

theorem prime_110567 : Nat.Prime 110567 := by
  apply nodeValid_prime [2, 59, 937] ⟨110567, 5, [(2, 1), (59, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_937
  · decide +kernel

theorem prime_125591 : Nat.Prime 125591 := by
  apply nodeValid_prime [2, 5, 19, 661] ⟨125591, 11, [(2, 1), (5, 1), (19, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_661
  · decide +kernel

theorem prime_154871 : Nat.Prime 154871 := by
  apply nodeValid_prime [2, 5, 17, 911] ⟨154871, 13, [(2, 1), (5, 1), (17, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_911
  · decide +kernel

theorem prime_155699 : Nat.Prime 155699 := by
  apply nodeValid_prime [2, 77849] ⟨155699, 2, [(2, 1), (77849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_77849
  · decide +kernel

theorem prime_193493 : Nat.Prime 193493 := by
  apply nodeValid_prime [2, 13, 61] ⟨193493, 2, [(2, 2), (13, 1), (61, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_197677 : Nat.Prime 197677 := by
  apply nodeValid_prime [2, 3, 17, 19] ⟨197677, 5, [(2, 2), (3, 2), (17, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_215959 : Nat.Prime 215959 := by
  apply nodeValid_prime [2, 3, 35993] ⟨215959, 6, [(2, 1), (3, 1), (35993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35993
  · decide +kernel

theorem prime_217003 : Nat.Prime 217003 := by
  apply nodeValid_prime [2, 3, 59, 613] ⟨217003, 3, [(2, 1), (3, 1), (59, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_613
  · decide +kernel

theorem prime_222587 : Nat.Prime 222587 := by
  apply nodeValid_prime [2, 7, 13, 1223] ⟨222587, 2, [(2, 1), (7, 1), (13, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1223
  · decide +kernel

theorem prime_236891 : Nat.Prime 236891 := by
  apply nodeValid_prime [2, 5, 23689] ⟨236891, 2, [(2, 1), (5, 1), (23689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23689
  · decide +kernel

theorem prime_301601 : Nat.Prime 301601 := by
  apply nodeValid_prime [2, 5, 13, 29] ⟨301601, 6, [(2, 5), (5, 2), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_314077 : Nat.Prime 314077 := by
  apply nodeValid_prime [2, 3, 7, 3739] ⟨314077, 2, [(2, 2), (3, 1), (7, 1), (3739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3739
  · decide +kernel

theorem prime_331217 : Nat.Prime 331217 := by
  apply nodeValid_prime [2, 127, 163] ⟨331217, 3, [(2, 4), (127, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_163
  · decide +kernel

theorem prime_502487 : Nat.Prime 502487 := by
  apply nodeValid_prime [2, 17, 14779] ⟨502487, 5, [(2, 1), (17, 1), (14779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_14779
  · decide +kernel

theorem prime_644291 : Nat.Prime 644291 := by
  apply nodeValid_prime [2, 5, 19, 3391] ⟨644291, 2, [(2, 1), (5, 1), (19, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3391
  · decide +kernel

theorem prime_753547 : Nat.Prime 753547 := by
  apply nodeValid_prime [2, 3, 125591] ⟨753547, 2, [(2, 1), (3, 1), (125591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_125591
  · decide +kernel

theorem prime_790709 : Nat.Prime 790709 := by
  apply nodeValid_prime [2, 197677] ⟨790709, 2, [(2, 2), (197677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_197677
  · decide +kernel

theorem prime_855947 : Nat.Prime 855947 := by
  apply nodeValid_prime [2, 7, 13, 4703] ⟨855947, 2, [(2, 1), (7, 1), (13, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_4703
  · decide +kernel

theorem prime_884537 : Nat.Prime 884537 := by
  apply nodeValid_prime [2, 110567] ⟨884537, 3, [(2, 3), (110567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_110567
  · decide +kernel

theorem prime_1022977 : Nat.Prime 1022977 := by
  apply nodeValid_prime [2, 3, 37] ⟨1022977, 5, [(2, 10), (3, 3), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel

theorem prime_1156613 : Nat.Prime 1156613 := by
  apply nodeValid_prime [2, 17, 73, 233] ⟨1156613, 2, [(2, 2), (17, 1), (73, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_73
    · exact prime_233
  · decide +kernel

theorem prime_1417057 : Nat.Prime 1417057 := by
  apply nodeValid_prime [2, 3, 29, 509] ⟨1417057, 5, [(2, 5), (3, 1), (29, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_509
  · decide +kernel

theorem prime_1464343 : Nat.Prime 1464343 := by
  apply nodeValid_prime [2, 3, 11, 2017] ⟨1464343, 17, [(2, 1), (3, 1), (11, 2), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2017
  · decide +kernel

theorem prime_1516103 : Nat.Prime 1516103 := by
  apply nodeValid_prime [2, 7, 108293] ⟨1516103, 5, [(2, 1), (7, 1), (108293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_108293
  · decide +kernel

theorem prime_1588933 : Nat.Prime 1588933 := by
  apply nodeValid_prime [2, 3, 19, 23, 101] ⟨1588933, 2, [(2, 2), (3, 2), (19, 1), (23, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_101
  · decide +kernel

theorem prime_1593401 : Nat.Prime 1593401 := by
  apply nodeValid_prime [2, 5, 31, 257] ⟨1593401, 3, [(2, 3), (5, 2), (31, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_257
  · decide +kernel

theorem prime_1616227 : Nat.Prime 1616227 := by
  apply nodeValid_prime [2, 3, 167, 1613] ⟨1616227, 5, [(2, 1), (3, 1), (167, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_1613
  · decide +kernel

theorem prime_1803023 : Nat.Prime 1803023 := by
  apply nodeValid_prime [2, 13, 31, 2237] ⟨1803023, 5, [(2, 1), (13, 1), (31, 1), (2237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_2237
  · decide +kernel

theorem prime_1877233 : Nat.Prime 1877233 := by
  apply nodeValid_prime [2, 3, 7, 37, 151] ⟨1877233, 5, [(2, 4), (3, 1), (7, 1), (37, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_151
  · decide +kernel

theorem prime_2563763 : Nat.Prime 2563763 := by
  apply nodeValid_prime [2, 31, 41351] ⟨2563763, 2, [(2, 1), (31, 1), (41351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41351
  · decide +kernel

theorem prime_2697571 : Nat.Prime 2697571 := by
  apply nodeValid_prime [2, 3, 5, 97, 103] ⟨2697571, 38, [(2, 1), (3, 3), (5, 1), (97, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_97
    · exact prime_103
  · decide +kernel

theorem prime_2697599 : Nat.Prime 2697599 := by
  apply nodeValid_prime [2, 59, 22861] ⟨2697599, 7, [(2, 1), (59, 1), (22861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_22861
  · decide +kernel

theorem prime_2858333 : Nat.Prime 2858333 := by
  apply nodeValid_prime [2, 281, 2543] ⟨2858333, 2, [(2, 2), (281, 1), (2543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_2543
  · decide +kernel

theorem prime_3002473 : Nat.Prime 3002473 := by
  apply nodeValid_prime [2, 3, 11, 17, 223] ⟨3002473, 7, [(2, 3), (3, 2), (11, 1), (17, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_223
  · decide +kernel

theorem prime_3032207 : Nat.Prime 3032207 := by
  apply nodeValid_prime [2, 1516103] ⟨3032207, 5, [(2, 1), (1516103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1516103
  · decide +kernel

theorem prime_3792253 : Nat.Prime 3792253 := by
  apply nodeValid_prime [2, 3, 71, 4451] ⟨3792253, 2, [(2, 2), (3, 1), (71, 1), (4451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_4451
  · decide +kernel

theorem prime_6035957 : Nat.Prime 6035957 := by
  apply nodeValid_prime [2, 131, 11519] ⟨6035957, 2, [(2, 2), (131, 1), (11519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_11519
  · decide +kernel

theorem prime_6050507 : Nat.Prime 6050507 := by
  apply nodeValid_prime [2, 7, 11, 101, 389] ⟨6050507, 2, [(2, 1), (7, 1), (11, 1), (101, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_101
    · exact prime_389
  · decide +kernel

theorem prime_6273937 : Nat.Prime 6273937 := by
  apply nodeValid_prime [2, 3, 47, 103] ⟨6273937, 5, [(2, 4), (3, 4), (47, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_103
  · decide +kernel

theorem prime_6939679 : Nat.Prime 6939679 := by
  apply nodeValid_prime [2, 3, 1156613] ⟨6939679, 3, [(2, 1), (3, 1), (1156613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1156613
  · decide +kernel

theorem prime_7860191 : Nat.Prime 7860191 := by
  apply nodeValid_prime [2, 5, 13, 4651] ⟨7860191, 11, [(2, 1), (5, 1), (13, 2), (4651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4651
  · decide +kernel

theorem prime_7980997 : Nat.Prime 7980997 := by
  apply nodeValid_prime [2, 3, 61, 10903] ⟨7980997, 5, [(2, 2), (3, 1), (61, 1), (10903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_10903
  · decide +kernel

theorem prime_8502343 : Nat.Prime 8502343 := by
  apply nodeValid_prime [2, 3, 1417057] ⟨8502343, 5, [(2, 1), (3, 1), (1417057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1417057
  · decide +kernel

theorem prime_11935783 : Nat.Prime 11935783 := by
  apply nodeValid_prime [2, 3, 67, 3299] ⟨11935783, 3, [(2, 1), (3, 3), (67, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_3299
  · decide +kernel

theorem prime_12451489 : Nat.Prime 12451489 := by
  apply nodeValid_prime [2, 3, 7, 2647] ⟨12451489, 11, [(2, 5), (3, 1), (7, 2), (2647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2647
  · decide +kernel

theorem prime_14397367 : Nat.Prime 14397367 := by
  apply nodeValid_prime [2, 3, 37, 64853] ⟨14397367, 3, [(2, 1), (3, 1), (37, 1), (64853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_64853
  · decide +kernel

theorem prime_15665521 : Nat.Prime 15665521 := by
  apply nodeValid_prime [2, 3, 5, 13, 5021] ⟨15665521, 19, [(2, 4), (3, 1), (5, 1), (13, 1), (5021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_5021
  · decide +kernel

theorem prime_17572117 : Nat.Prime 17572117 := by
  apply nodeValid_prime [2, 3, 1464343] ⟨17572117, 2, [(2, 2), (3, 1), (1464343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1464343
  · decide +kernel

theorem prime_22109429 : Nat.Prime 22109429 := by
  apply nodeValid_prime [2, 11, 502487] ⟨22109429, 3, [(2, 2), (11, 1), (502487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_502487
  · decide +kernel

theorem prime_22997963 : Nat.Prime 22997963 := by
  apply nodeValid_prime [2, 13, 884537] ⟨22997963, 2, [(2, 1), (13, 1), (884537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_884537
  · decide +kernel

theorem prime_38728097 : Nat.Prime 38728097 := by
  apply nodeValid_prime [2, 11, 110023] ⟨38728097, 3, [(2, 5), (11, 1), (110023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_110023
  · decide +kernel

theorem prime_83189063 : Nat.Prime 83189063 := by
  apply nodeValid_prime [2, 11, 463, 8167] ⟨83189063, 5, [(2, 1), (11, 1), (463, 1), (8167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_463
    · exact prime_8167
  · decide +kernel

theorem prime_90151151 : Nat.Prime 90151151 := by
  apply nodeValid_prime [2, 5, 1803023] ⟨90151151, 23, [(2, 1), (5, 2), (1803023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1803023
  · decide +kernel

theorem prime_98484131 : Nat.Prime 98484131 := by
  apply nodeValid_prime [2, 5, 2741, 3593] ⟨98484131, 2, [(2, 1), (5, 1), (2741, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2741
    · exact prime_3593
  · decide +kernel

theorem prime_121046813 : Nat.Prime 121046813 := by
  apply nodeValid_prime [2, 29, 35983] ⟨121046813, 2, [(2, 2), (29, 2), (35983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_35983
  · decide +kernel

theorem prime_148003253 : Nat.Prime 148003253 := by
  apply nodeValid_prime [2, 23, 109, 14759] ⟨148003253, 2, [(2, 2), (23, 1), (109, 1), (14759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_109
    · exact prime_14759
  · decide +kernel

theorem prime_180500107 : Nat.Prime 180500107 := by
  apply nodeValid_prime [2, 3, 953, 31567] ⟨180500107, 3, [(2, 1), (3, 1), (953, 1), (31567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_953
    · exact prime_31567
  · decide +kernel

theorem prime_217496801 : Nat.Prime 217496801 := by
  apply nodeValid_prime [2, 5, 19, 41, 349] ⟨217496801, 3, [(2, 5), (5, 2), (19, 1), (41, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_349
  · decide +kernel

theorem prime_255969157 : Nat.Prime 255969157 := by
  apply nodeValid_prime [2, 3, 137, 155699] ⟨255969157, 2, [(2, 2), (3, 1), (137, 1), (155699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_155699
  · decide +kernel

theorem prime_264677549 : Nat.Prime 264677549 := by
  apply nodeValid_prime [2, 29, 53, 43051] ⟨264677549, 2, [(2, 2), (29, 1), (53, 1), (43051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_53
    · exact prime_43051
  · decide +kernel

theorem prime_285507031 : Nat.Prime 285507031 := by
  apply nodeValid_prime [2, 3, 5, 29, 107, 3067] ⟨285507031, 6, [(2, 1), (3, 1), (5, 1), (29, 1), (107, 1), (3067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_107
    · exact prime_3067
  · decide +kernel

theorem prime_335578081 : Nat.Prime 335578081 := by
  apply nodeValid_prime [2, 3, 5, 61, 73, 157] ⟨335578081, 7, [(2, 5), (3, 1), (5, 1), (61, 1), (73, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_73
    · exact prime_157
  · decide +kernel

theorem prime_372674383 : Nat.Prime 372674383 := by
  apply nodeValid_prime [2, 3, 23, 547, 4937] ⟨372674383, 7, [(2, 1), (3, 1), (23, 1), (547, 1), (4937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_547
    · exact prime_4937
  · decide +kernel

theorem prime_405092209 : Nat.Prime 405092209 := by
  apply nodeValid_prime [2, 3, 2039, 4139] ⟨405092209, 13, [(2, 4), (3, 1), (2039, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2039
    · exact prime_4139
  · decide +kernel

theorem prime_875110573 : Nat.Prime 875110573 := by
  apply nodeValid_prime [2, 3, 7, 383, 9067] ⟨875110573, 2, [(2, 2), (3, 2), (7, 1), (383, 1), (9067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_383
    · exact prime_9067
  · decide +kernel

theorem prime_888019519 : Nat.Prime 888019519 := by
  apply nodeValid_prime [2, 3, 148003253] ⟨888019519, 3, [(2, 1), (3, 1), (148003253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_148003253
  · decide +kernel

theorem prime_1007229679 : Nat.Prime 1007229679 := by
  apply nodeValid_prime [2, 3, 7, 13, 43, 42901] ⟨1007229679, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (43, 1), (42901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_42901
  · decide +kernel

theorem prime_2013468487 : Nat.Prime 2013468487 := by
  apply nodeValid_prime [2, 3, 335578081] ⟨2013468487, 3, [(2, 1), (3, 1), (335578081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_335578081
  · decide +kernel

theorem prime_2154054047 : Nat.Prime 2154054047 := by
  apply nodeValid_prime [2, 383, 389, 7229] ⟨2154054047, 5, [(2, 1), (383, 1), (389, 1), (7229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_383
    · exact prime_389
    · exact prime_7229
  · decide +kernel

theorem prime_2251700939 : Nat.Prime 2251700939 := by
  apply nodeValid_prime [2, 107, 197, 53411] ⟨2251700939, 2, [(2, 1), (107, 1), (197, 1), (53411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_197
    · exact prime_53411
  · decide +kernel

theorem prime_2522742793 : Nat.Prime 2522742793 := by
  apply nodeValid_prime [2, 3, 41, 2563763] ⟨2522742793, 10, [(2, 3), (3, 1), (41, 1), (2563763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_2563763
  · decide +kernel

theorem prime_2807150809 : Nat.Prime 2807150809 := by
  apply nodeValid_prime [2, 3, 7, 11, 217003] ⟨2807150809, 19, [(2, 3), (3, 1), (7, 2), (11, 1), (217003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_217003
  · decide +kernel

theorem prime_3793876949 : Nat.Prime 3793876949 := by
  apply nodeValid_prime [2, 241, 461, 8537] ⟨3793876949, 2, [(2, 2), (241, 1), (461, 1), (8537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_461
    · exact prime_8537
  · decide +kernel

theorem prime_3813950401 : Nat.Prime 3813950401 := by
  apply nodeValid_prime [2, 3, 5, 13, 61121] ⟨3813950401, 19, [(2, 6), (3, 1), (5, 2), (13, 1), (61121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_61121
  · decide +kernel

theorem prime_5038334347 : Nat.Prime 5038334347 := by
  apply nodeValid_prime [2, 3, 12527, 67033] ⟨5038334347, 2, [(2, 1), (3, 1), (12527, 1), (67033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12527
    · exact prime_67033
  · decide +kernel

theorem prime_6406283887 : Nat.Prime 6406283887 := by
  apply nodeValid_prime [2, 3, 23, 4129, 11243] ⟨6406283887, 3, [(2, 1), (3, 1), (23, 1), (4129, 1), (11243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_4129
    · exact prime_11243
  · decide +kernel

theorem prime_6490882873 : Nat.Prime 6490882873 := by
  apply nodeValid_prime [2, 3, 90151151] ⟨6490882873, 5, [(2, 3), (3, 2), (90151151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_90151151
  · decide +kernel

theorem prime_7965881687 : Nat.Prime 7965881687 := by
  apply nodeValid_prime [2, 7, 23, 1237, 2857] ⟨7965881687, 5, [(2, 1), (7, 2), (23, 1), (1237, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_1237
    · exact prime_2857
  · decide +kernel

theorem prime_9181712909 : Nat.Prime 9181712909 := by
  apply nodeValid_prime [2, 2903, 790709] ⟨9181712909, 2, [(2, 2), (2903, 1), (790709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2903
    · exact prime_790709
  · decide +kernel

theorem prime_9664664351 : Nat.Prime 9664664351 := by
  apply nodeValid_prime [2, 5, 11, 17572117] ⟨9664664351, 11, [(2, 1), (5, 2), (11, 1), (17572117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17572117
  · decide +kernel

theorem prime_11947308227 : Nat.Prime 11947308227 := by
  apply nodeValid_prime [2, 7, 997, 855947] ⟨11947308227, 2, [(2, 1), (7, 1), (997, 1), (855947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_997
    · exact prime_855947
  · decide +kernel

theorem prime_14113827647 : Nat.Prime 14113827647 := by
  apply nodeValid_prime [2, 19, 167, 541, 4111] ⟨14113827647, 5, [(2, 1), (19, 1), (167, 1), (541, 1), (4111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_167
    · exact prime_541
    · exact prime_4111
  · decide +kernel

theorem prime_18363425819 : Nat.Prime 18363425819 := by
  apply nodeValid_prime [2, 9181712909] ⟨18363425819, 2, [(2, 1), (9181712909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9181712909
  · decide +kernel

theorem prime_22468440427 : Nat.Prime 22468440427 := by
  apply nodeValid_prime [2, 3, 11923, 314077] ⟨22468440427, 3, [(2, 1), (3, 1), (11923, 1), (314077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11923
    · exact prime_314077
  · decide +kernel

theorem prime_23875597919 : Nat.Prime 23875597919 := by
  apply nodeValid_prime [2, 31, 127, 3032207] ⟨23875597919, 17, [(2, 1), (31, 1), (127, 1), (3032207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_127
    · exact prime_3032207
  · decide +kernel

theorem prime_26524948217 : Nat.Prime 26524948217 := by
  apply nodeValid_prime [2, 13, 1181, 215959] ⟨26524948217, 3, [(2, 3), (13, 1), (1181, 1), (215959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1181
    · exact prime_215959
  · decide +kernel

theorem prime_26895959891 : Nat.Prime 26895959891 := by
  apply nodeValid_prime [2, 5, 337, 7980997] ⟨26895959891, 2, [(2, 1), (5, 1), (337, 1), (7980997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_337
    · exact prime_7980997
  · decide +kernel

theorem prime_29503728341 : Nat.Prime 29503728341 := by
  apply nodeValid_prime [2, 5, 389, 3792253] ⟨29503728341, 2, [(2, 2), (5, 1), (389, 1), (3792253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_389
    · exact prime_3792253
  · decide +kernel

theorem prime_36175520741 : Nat.Prime 36175520741 := by
  apply nodeValid_prime [2, 5, 43, 127, 331217] ⟨36175520741, 3, [(2, 2), (5, 1), (43, 1), (127, 1), (331217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_127
    · exact prime_331217
  · decide +kernel

theorem prime_36726851639 : Nat.Prime 36726851639 := by
  apply nodeValid_prime [2, 18363425819] ⟨36726851639, 7, [(2, 1), (18363425819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_18363425819
  · decide +kernel

theorem prime_55192600123 : Nat.Prime 55192600123 := by
  apply nodeValid_prime [2, 3, 11, 23279, 35923] ⟨55192600123, 2, [(2, 1), (3, 1), (11, 1), (23279, 1), (35923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23279
    · exact prime_35923
  · decide +kernel

theorem prime_62218185283 : Nat.Prime 62218185283 := by
  apply nodeValid_prime [2, 3, 11, 2029, 154871] ⟨62218185283, 2, [(2, 1), (3, 2), (11, 1), (2029, 1), (154871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2029
    · exact prime_154871
  · decide +kernel

theorem prime_79648724647 : Nat.Prime 79648724647 := by
  apply nodeValid_prime [2, 3, 43, 1061, 96989] ⟨79648724647, 5, [(2, 1), (3, 2), (43, 1), (1061, 1), (96989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1061
    · exact prime_96989
  · decide +kernel

theorem prime_121591850707 : Nat.Prime 121591850707 := by
  apply nodeValid_prime [2, 3, 2251700939] ⟨121591850707, 5, [(2, 1), (3, 3), (2251700939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2251700939
  · decide +kernel

theorem prime_204241449959 : Nat.Prime 204241449959 := by
  apply nodeValid_prime [2, 7, 13, 1097, 1022977] ⟨204241449959, 7, [(2, 1), (7, 1), (13, 1), (1097, 1), (1022977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1097
    · exact prime_1022977
  · decide +kernel

theorem prime_286735397449 : Nat.Prime 286735397449 := by
  apply nodeValid_prime [2, 3, 11947308227] ⟨286735397449, 11, [(2, 3), (3, 1), (11947308227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11947308227
  · decide +kernel

theorem prime_289671967807 : Nat.Prime 289671967807 := by
  apply nodeValid_prime [2, 3, 13, 17, 31, 103, 2207] ⟨289671967807, 5, [(2, 1), (3, 1), (13, 1), (17, 1), (31, 2), (103, 1), (2207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_31
    · exact prime_103
    · exact prime_2207
  · decide +kernel

theorem prime_359751128237 : Nat.Prime 359751128237 := by
  apply nodeValid_prime [2, 743, 121046813] ⟨359751128237, 2, [(2, 2), (743, 1), (121046813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_743
    · exact prime_121046813
  · decide +kernel

theorem prime_1436339083391 : Nat.Prime 1436339083391 := by
  apply nodeValid_prime [2, 5, 29, 46831, 105761] ⟨1436339083391, 7, [(2, 1), (5, 1), (29, 1), (46831, 1), (105761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_46831
    · exact prime_105761
  · decide +kernel

theorem prime_1436339084249 : Nat.Prime 1436339084249 := by
  apply nodeValid_prime [2, 823, 2347, 92951] ⟨1436339084249, 3, [(2, 3), (823, 1), (2347, 1), (92951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_823
    · exact prime_2347
    · exact prime_92951
  · decide +kernel

theorem prime_1441673240621 : Nat.Prime 1441673240621 := by
  apply nodeValid_prime [2, 5, 19, 3793876949] ⟨1441673240621, 2, [(2, 2), (5, 1), (19, 1), (3793876949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3793876949
  · decide +kernel

theorem prime_2859380281981 : Nat.Prime 2859380281981 := by
  apply nodeValid_prime [2, 3, 5, 43, 47, 7860191] ⟨2859380281981, 13, [(2, 2), (3, 2), (5, 1), (43, 1), (47, 1), (7860191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_47
    · exact prime_7860191
  · decide +kernel

theorem prime_2859380298661 : Nat.Prime 2859380298661 := by
  apply nodeValid_prime [2, 3, 5, 257, 3671, 50513] ⟨2859380298661, 2, [(2, 2), (3, 1), (5, 1), (257, 1), (3671, 1), (50513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
    · exact prime_3671
    · exact prime_50513
  · decide +kernel

theorem prime_2859380299427 : Nat.Prime 2859380299427 := by
  apply nodeValid_prime [2, 7, 204241449959] ⟨2859380299427, 2, [(2, 1), (7, 1), (204241449959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_204241449959
  · decide +kernel

theorem prime_2862036508729 : Nat.Prime 2862036508729 := by
  apply nodeValid_prime [2, 3, 44207, 2697571] ⟨2862036508729, 11, [(2, 3), (3, 1), (44207, 1), (2697571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44207
    · exact prime_2697571
  · decide +kernel

theorem prime_2862036523019 : Nat.Prime 2862036523019 := by
  apply nodeValid_prime [2, 23, 62218185283] ⟨2862036523019, 2, [(2, 1), (23, 1), (62218185283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_62218185283
  · decide +kernel

theorem prime_2862036523453 : Nat.Prime 2862036523453 := by
  apply nodeValid_prime [2, 3, 47, 61, 83189063] ⟨2862036523453, 2, [(2, 2), (3, 1), (47, 1), (61, 1), (83189063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_61
    · exact prime_83189063
  · decide +kernel

theorem prime_2864694407437 : Nat.Prime 2864694407437 := by
  apply nodeValid_prime [2, 3, 26524948217] ⟨2864694407437, 5, [(2, 2), (3, 3), (26524948217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26524948217
  · decide +kernel

theorem prime_2864694426991 : Nat.Prime 2864694426991 := by
  apply nodeValid_prime [2, 3, 5, 11, 1021, 8502343] ⟨2864694426991, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (1021, 1), (8502343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1021
    · exact prime_8502343
  · decide +kernel

theorem prime_2864694427843 : Nat.Prime 2864694427843 := by
  apply nodeValid_prime [2, 3, 13, 36726851639] ⟨2864694427843, 3, [(2, 1), (3, 1), (13, 1), (36726851639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_36726851639
  · decide +kernel

theorem prime_2867353974491 : Nat.Prime 2867353974491 := by
  apply nodeValid_prime [2, 5, 286735397449] ⟨2867353974491, 2, [(2, 1), (5, 1), (286735397449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_286735397449
  · decide +kernel

theorem prime_2867354086661 : Nat.Prime 2867354086661 := by
  apply nodeValid_prime [2, 5, 7, 311, 2273, 4139] ⟨2867354086661, 2, [(2, 2), (5, 1), (7, 2), (311, 1), (2273, 1), (4139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_311
    · exact prime_2273
    · exact prime_4139
  · decide +kernel

theorem prime_2867354087293 : Nat.Prime 2867354087293 := by
  apply nodeValid_prime [2, 3, 79648724647] ⟨2867354087293, 6, [(2, 2), (3, 2), (79648724647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79648724647
  · decide +kernel

theorem prime_2870015180983 : Nat.Prime 2870015180983 := by
  apply nodeValid_prime [2, 3, 19, 13411, 1877233] ⟨2870015180983, 5, [(2, 1), (3, 1), (19, 1), (13411, 1), (1877233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_13411
    · exact prime_1877233
  · decide +kernel

theorem prime_2870015181377 : Nat.Prime 2870015181377 := by
  apply nodeValid_prime [2, 7, 6406283887] ⟨2870015181377, 3, [(2, 6), (7, 1), (6406283887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_6406283887
  · decide +kernel

theorem prime_2870015206397 : Nat.Prime 2870015206397 := by
  apply nodeValid_prime [2, 13, 55192600123] ⟨2870015206397, 2, [(2, 2), (13, 1), (55192600123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_55192600123
  · decide +kernel

theorem prime_2872678109971 : Nat.Prime 2872678109971 := by
  apply nodeValid_prime [2, 3, 5, 61, 71, 22109429] ⟨2872678109971, 3, [(2, 1), (3, 1), (5, 1), (61, 1), (71, 1), (22109429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_71
    · exact prime_22109429
  · decide +kernel

theorem prime_2872678166783 : Nat.Prime 2872678166783 := by
  apply nodeValid_prime [2, 1436339083391] ⟨2872678166783, 5, [(2, 1), (1436339083391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1436339083391
  · decide +kernel

theorem prime_2872678168499 : Nat.Prime 2872678168499 := by
  apply nodeValid_prime [2, 1436339084249] ⟨2872678168499, 2, [(2, 1), (1436339084249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1436339084249
  · decide +kernel

theorem prime_2875342688677 : Nat.Prime 2875342688677 := by
  apply nodeValid_prime [2, 3, 811, 98484131] ⟨2875342688677, 6, [(2, 2), (3, 2), (811, 1), (98484131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
    · exact prime_98484131
  · decide +kernel

theorem prime_2875342690399 : Nat.Prime 2875342690399 := by
  apply nodeValid_prime [2, 3, 301601, 1588933] ⟨2875342690399, 3, [(2, 1), (3, 1), (301601, 1), (1588933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_301601
    · exact prime_1588933
  · decide +kernel

theorem prime_2878008953993 : Nat.Prime 2878008953993 := by
  apply nodeValid_prime [2, 222587, 1616227] ⟨2878008953993, 3, [(2, 3), (222587, 1), (1616227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_222587
    · exact prime_1616227
  · decide +kernel

theorem prime_2878009025897 : Nat.Prime 2878009025897 := by
  apply nodeValid_prime [2, 359751128237] ⟨2878009025897, 3, [(2, 3), (359751128237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_359751128237
  · decide +kernel

theorem prime_2878009025923 : Nat.Prime 2878009025923 := by
  apply nodeValid_prime [2, 3, 23, 859, 2697599] ⟨2878009025923, 2, [(2, 1), (3, 3), (23, 1), (859, 1), (2697599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_859
    · exact prime_2697599
  · decide +kernel

theorem prime_2880676881941 : Nat.Prime 2880676881941 := by
  apply nodeValid_prime [2, 5, 11, 13, 1007229679] ⟨2880676881941, 2, [(2, 2), (5, 1), (11, 1), (13, 1), (1007229679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_1007229679
  · decide +kernel

theorem prime_2880676883129 : Nat.Prime 2880676883129 := by
  apply nodeValid_prime [2, 11, 239, 12451489] ⟨2880676883129, 3, [(2, 3), (11, 2), (239, 1), (12451489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_239
    · exact prime_12451489
  · decide +kernel

theorem prime_2880676892879 : Nat.Prime 2880676892879 := by
  apply nodeValid_prime [2, 17, 331, 255969157] ⟨2880676892879, 7, [(2, 1), (17, 1), (331, 1), (255969157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_331
    · exact prime_255969157
  · decide +kernel

theorem prime_2883346480031 : Nat.Prime 2883346480031 := by
  apply nodeValid_prime [2, 5, 67, 39409, 109201] ⟨2883346480031, 17, [(2, 1), (5, 1), (67, 1), (39409, 1), (109201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_67
    · exact prime_39409
    · exact prime_109201
  · decide +kernel

theorem prime_2883346481243 : Nat.Prime 2883346481243 := by
  apply nodeValid_prime [2, 1441673240621] ⟨2883346481243, 2, [(2, 1), (1441673240621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1441673240621
  · decide +kernel

theorem prime_2883346503157 : Nat.Prime 2883346503157 := by
  apply nodeValid_prime [2, 3, 7, 3813950401] ⟨2883346503157, 2, [(2, 2), (3, 3), (7, 1), (3813950401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3813950401
  · decide +kernel

theorem prime_2886017752481 : Nat.Prime 2886017752481 := by
  apply nodeValid_prime [2, 5, 73, 1277, 193493] ⟨2886017752481, 3, [(2, 5), (5, 1), (73, 1), (1277, 1), (193493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_1277
    · exact prime_193493
  · decide +kernel

theorem prime_2886017755193 : Nat.Prime 2886017755193 := by
  apply nodeValid_prime [2, 11, 13, 2522742793] ⟨2886017755193, 3, [(2, 3), (11, 1), (13, 1), (2522742793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_2522742793
  · decide +kernel

theorem prime_2886017788441 : Nat.Prime 2886017788441 := by
  apply nodeValid_prime [2, 3, 5, 23, 38728097] ⟨2886017788441, 13, [(2, 3), (3, 4), (5, 1), (23, 1), (38728097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_38728097
  · decide +kernel

theorem prime_2888690741359 : Nat.Prime 2888690741359 := by
  apply nodeValid_prime [2, 3, 73, 421, 15665521] ⟨2888690741359, 11, [(2, 1), (3, 1), (73, 1), (421, 1), (15665521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_421
    · exact prime_15665521
  · decide +kernel

theorem prime_2888690766589 : Nat.Prime 2888690766589 := by
  apply nodeValid_prime [2, 3, 11, 521, 727, 19259] ⟨2888690766589, 2, [(2, 2), (3, 2), (11, 1), (521, 1), (727, 1), (19259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_521
    · exact prime_727
    · exact prime_19259
  · decide +kernel

theorem prime_2888690769787 : Nat.Prime 2888690769787 := by
  apply nodeValid_prime [2, 3, 17, 107, 264677549] ⟨2888690769787, 3, [(2, 1), (3, 1), (17, 1), (107, 1), (264677549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_107
    · exact prime_264677549
  · decide +kernel

theorem prime_2891365333193 : Nat.Prime 2891365333193 := by
  apply nodeValid_prime [2, 7, 59, 875110573] ⟨2891365333193, 3, [(2, 3), (7, 1), (59, 1), (875110573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_875110573
  · decide +kernel

theorem prime_2891365333271 : Nat.Prime 2891365333271 := by
  apply nodeValid_prime [2, 5, 103, 2807150809] ⟨2891365333271, 7, [(2, 1), (5, 1), (103, 1), (2807150809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_2807150809
  · decide +kernel

theorem prime_2891365377419 : Nat.Prime 2891365377419 := by
  apply nodeValid_prime [2, 7, 29503728341] ⟨2891365377419, 2, [(2, 1), (7, 2), (29503728341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29503728341
  · decide +kernel

theorem prime_2894041659281 : Nat.Prime 2894041659281 := by
  apply nodeValid_prime [2, 5, 36175520741] ⟨2894041659281, 3, [(2, 4), (5, 1), (36175520741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_36175520741
  · decide +kernel

theorem prime_2894041659361 : Nat.Prime 2894041659361 := by
  apply nodeValid_prime [2, 3, 5, 31, 6273937] ⟨2894041659361, 11, [(2, 5), (3, 1), (5, 1), (31, 2), (6273937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_6273937
  · decide +kernel

theorem prime_2894041690079 : Nat.Prime 2894041690079 := by
  apply nodeValid_prime [2, 7, 11, 569, 3002473] ⟨2894041690079, 7, [(2, 1), (7, 1), (11, 2), (569, 1), (3002473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_569
    · exact prime_3002473
  · decide +kernel

theorem prime_2896719670979 : Nat.Prime 2896719670979 := by
  apply nodeValid_prime [2, 7, 233, 888019519] ⟨2896719670979, 2, [(2, 1), (7, 1), (233, 1), (888019519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_233
    · exact prime_888019519
  · decide +kernel

theorem prime_2896719674087 : Nat.Prime 2896719674087 := by
  apply nodeValid_prime [2, 7, 109, 30971, 61291] ⟨2896719674087, 5, [(2, 1), (7, 1), (109, 1), (30971, 1), (61291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109
    · exact prime_30971
    · exact prime_61291
  · decide +kernel

theorem prime_2896719678071 : Nat.Prime 2896719678071 := by
  apply nodeValid_prime [2, 5, 289671967807] ⟨2896719678071, 7, [(2, 1), (5, 1), (289671967807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_289671967807
  · decide +kernel

theorem prime_2899399305301 : Nat.Prime 2899399305301 := by
  apply nodeValid_prime [2, 3, 5, 9664664351] ⟨2899399305301, 2, [(2, 2), (3, 1), (5, 2), (9664664351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9664664351
  · decide +kernel

theorem prime_2899399306627 : Nat.Prime 2899399306627 := by
  apply nodeValid_prime [2, 3, 607, 11731, 22621] ⟨2899399306627, 2, [(2, 1), (3, 2), (607, 1), (11731, 1), (22621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_607
    · exact prime_11731
    · exact prime_22621
  · decide +kernel

theorem prime_2899399355929 : Nat.Prime 2899399355929 := by
  apply nodeValid_prime [2, 3, 2797, 14397367] ⟨2899399355929, 7, [(2, 3), (3, 2), (2797, 1), (14397367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2797
    · exact prime_14397367
  · decide +kernel

theorem prime_2902080583873 : Nat.Prime 2902080583873 := by
  apply nodeValid_prime [2, 3, 5038334347] ⟨2902080583873, 5, [(2, 6), (3, 2), (5038334347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5038334347
  · decide +kernel

theorem prime_2902080585277 : Nat.Prime 2902080585277 := by
  apply nodeValid_prime [2, 3, 199, 405092209] ⟨2902080585277, 2, [(2, 2), (3, 2), (199, 1), (405092209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_405092209
  · decide +kernel

theorem prime_2902080720347 : Nat.Prime 2902080720347 := by
  apply nodeValid_prime [2, 8039, 180500107] ⟨2902080720347, 2, [(2, 1), (8039, 1), (180500107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8039
    · exact prime_180500107
  · decide +kernel

theorem prime_2904763668229 : Nat.Prime 2904763668229 := by
  apply nodeValid_prime [2, 3, 26895959891] ⟨2904763668229, 6, [(2, 2), (3, 3), (26895959891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26895959891
  · decide +kernel

theorem prime_2904763668733 : Nat.Prime 2904763668733 := by
  apply nodeValid_prime [2, 3, 349, 5479, 42197] ⟨2904763668733, 2, [(2, 2), (3, 2), (349, 1), (5479, 1), (42197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_5479
    · exact prime_42197
  · decide +kernel

theorem prime_2904763761253 : Nat.Prime 2904763761253 := by
  apply nodeValid_prime [2, 3, 28229, 2858333] ⟨2904763761253, 2, [(2, 2), (3, 2), (28229, 1), (2858333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28229
    · exact prime_2858333
  · decide +kernel

theorem prime_2907448478387 : Nat.Prime 2907448478387 := by
  apply nodeValid_prime [2, 63211, 22997963] ⟨2907448478387, 2, [(2, 1), (63211, 1), (22997963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_63211
    · exact prime_22997963
  · decide +kernel

theorem prime_2907448495229 : Nat.Prime 2907448495229 := by
  apply nodeValid_prime [2, 19, 2013468487] ⟨2907448495229, 2, [(2, 2), (19, 2), (2013468487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2013468487
  · decide +kernel

theorem prime_2907448495283 : Nat.Prime 2907448495283 := by
  apply nodeValid_prime [2, 103, 14113827647] ⟨2907448495283, 2, [(2, 1), (103, 1), (14113827647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_14113827647
  · decide +kernel

theorem prime_2910134867701 : Nat.Prime 2910134867701 := by
  apply nodeValid_prime [2, 3, 5, 40949, 236891] ⟨2910134867701, 10, [(2, 2), (3, 1), (5, 2), (40949, 1), (236891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_40949
    · exact prime_236891
  · decide +kernel

theorem prime_2910134867929 : Nat.Prime 2910134867929 := by
  apply nodeValid_prime [2, 3, 10159, 11935783] ⟨2910134867929, 17, [(2, 3), (3, 1), (10159, 1), (11935783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10159
    · exact prime_11935783
  · decide +kernel

theorem prime_2910134877383 : Nat.Prime 2910134877383 := by
  apply nodeValid_prime [2, 73, 30937, 644291] ⟨2910134877383, 5, [(2, 1), (73, 1), (30937, 1), (644291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_30937
    · exact prime_644291
  · decide +kernel

theorem prime_2912822946119 : Nat.Prime 2912822946119 := by
  apply nodeValid_prime [2, 61, 23875597919] ⟨2912822946119, 7, [(2, 1), (61, 1), (23875597919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_23875597919
  · decide +kernel

theorem prime_2912822977529 : Nat.Prime 2912822977529 := by
  apply nodeValid_prime [2, 977, 372674383] ⟨2912822977529, 3, [(2, 3), (977, 1), (372674383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_977
    · exact prime_372674383
  · decide +kernel

theorem prime_2912822978927 : Nat.Prime 2912822978927 := by
  apply nodeValid_prime [2, 7, 137, 251, 6050507] ⟨2912822978927, 5, [(2, 1), (7, 1), (137, 1), (251, 1), (6050507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_251
    · exact prime_6050507
  · decide +kernel

theorem prime_2915512697443 : Nat.Prime 2915512697443 := by
  apply nodeValid_prime [2, 3, 61, 7965881687] ⟨2915512697443, 2, [(2, 1), (3, 1), (61, 1), (7965881687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_7965881687
  · decide +kernel

theorem prime_2915512732357 : Nat.Prime 2915512732357 := by
  apply nodeValid_prime [2, 3, 7, 283, 3083, 5683] ⟨2915512732357, 2, [(2, 2), (3, 1), (7, 2), (283, 1), (3083, 1), (5683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_283
    · exact prime_3083
    · exact prime_5683
  · decide +kernel

theorem prime_2915512732543 : Nat.Prime 2915512732543 := by
  apply nodeValid_prime [2, 3, 23, 13259, 1593401] ⟨2915512732543, 5, [(2, 1), (3, 1), (23, 1), (13259, 1), (1593401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_13259
    · exact prime_1593401
  · decide +kernel

theorem prime_2918204130791 : Nat.Prime 2918204130791 := by
  apply nodeValid_prime [2, 5, 13, 3719, 6035957] ⟨2918204130791, 11, [(2, 1), (5, 1), (13, 1), (3719, 1), (6035957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_3719
    · exact prime_6035957
  · decide +kernel

theorem prime_2918204416291 : Nat.Prime 2918204416291 := by
  apply nodeValid_prime [2, 3, 5, 107, 131, 6939679] ⟨2918204416291, 2, [(2, 1), (3, 1), (5, 1), (107, 1), (131, 1), (6939679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
    · exact prime_131
    · exact prime_6939679
  · decide +kernel

theorem prime_2918204416969 : Nat.Prime 2918204416969 := by
  apply nodeValid_prime [2, 3, 121591850707] ⟨2918204416969, 33, [(2, 3), (3, 1), (121591850707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_121591850707
  · decide +kernel

theorem prime_2920897255511 : Nat.Prime 2920897255511 := by
  apply nodeValid_prime [2, 5, 13, 22468440427] ⟨2920897255511, 7, [(2, 1), (5, 1), (13, 1), (22468440427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_22468440427
  · decide +kernel

theorem prime_2920897287733 : Nat.Prime 2920897287733 := by
  apply nodeValid_prime [2, 3, 113, 2154054047] ⟨2920897287733, 2, [(2, 2), (3, 1), (113, 1), (2154054047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_2154054047
  · decide +kernel

theorem prime_2920897292851 : Nat.Prime 2920897292851 := by
  apply nodeValid_prime [2, 3, 5, 6490882873] ⟨2920897292851, 2, [(2, 1), (3, 2), (5, 2), (6490882873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6490882873
  · decide +kernel

theorem prime_2923591997441 : Nat.Prime 2923591997441 := by
  apply nodeValid_prime [2, 5, 285507031] ⟨2923591997441, 6, [(2, 11), (5, 1), (285507031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_285507031
  · decide +kernel

theorem prime_2923591999043 : Nat.Prime 2923591999043 := by
  apply nodeValid_prime [2, 11, 13, 47, 217496801] ⟨2923591999043, 2, [(2, 1), (11, 1), (13, 1), (47, 1), (217496801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_47
    · exact prime_217496801
  · decide +kernel

theorem prime_2923592058379 : Nat.Prime 2923592058379 := by
  apply nodeValid_prime [2, 3, 17, 31, 409, 753547] ⟨2923592058379, 2, [(2, 1), (3, 2), (17, 1), (31, 1), (409, 1), (753547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_409
    · exact prime_753547
  · decide +kernel

end Sude.Lucas.Generated
