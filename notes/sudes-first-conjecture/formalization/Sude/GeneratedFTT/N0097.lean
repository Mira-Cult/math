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
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0090
import Sude.GeneratedFTT.N0091

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11353 : Nat.Prime 11353 := by
  apply nodeValid_prime [2, 3, 11, 43] ⟨11353, 7, [(2, 3), (3, 1), (11, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
  · decide +kernel

theorem prime_12281 : Nat.Prime 12281 := by
  apply nodeValid_prime [2, 5, 307] ⟨12281, 3, [(2, 3), (5, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_307
  · decide +kernel

theorem prime_13103 : Nat.Prime 13103 := by
  apply nodeValid_prime [2, 6551] ⟨13103, 5, [(2, 1), (6551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6551
  · decide +kernel

theorem prime_17581 : Nat.Prime 17581 := by
  apply nodeValid_prime [2, 3, 5, 293] ⟨17581, 10, [(2, 2), (3, 1), (5, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_293
  · decide +kernel

theorem prime_28297 : Nat.Prime 28297 := by
  apply nodeValid_prime [2, 3, 131] ⟨28297, 5, [(2, 3), (3, 3), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_28921 : Nat.Prime 28921 := by
  apply nodeValid_prime [2, 3, 5, 241] ⟨28921, 11, [(2, 3), (3, 1), (5, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_30593 : Nat.Prime 30593 := by
  apply nodeValid_prime [2, 239] ⟨30593, 3, [(2, 7), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_239
  · decide +kernel

theorem prime_30703 : Nat.Prime 30703 := by
  apply nodeValid_prime [2, 3, 7, 17, 43] ⟨30703, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_32537 : Nat.Prime 32537 := by
  apply nodeValid_prime [2, 7, 83] ⟨32537, 3, [(2, 3), (7, 2), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_83
  · decide +kernel

theorem prime_36877 : Nat.Prime 36877 := by
  apply nodeValid_prime [2, 3, 7, 439] ⟨36877, 2, [(2, 2), (3, 1), (7, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_439
  · decide +kernel

theorem prime_42719 : Nat.Prime 42719 := by
  apply nodeValid_prime [2, 13, 31, 53] ⟨42719, 19, [(2, 1), (13, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_51929 : Nat.Prime 51929 := by
  apply nodeValid_prime [2, 6491] ⟨51929, 3, [(2, 3), (6491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6491
  · decide +kernel

theorem prime_53479 : Nat.Prime 53479 := by
  apply nodeValid_prime [2, 3, 2971] ⟨53479, 3, [(2, 1), (3, 2), (2971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2971
  · decide +kernel

theorem prime_56477 : Nat.Prime 56477 := by
  apply nodeValid_prime [2, 7, 2017] ⟨56477, 2, [(2, 2), (7, 1), (2017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2017
  · decide +kernel

theorem prime_59707 : Nat.Prime 59707 := by
  apply nodeValid_prime [2, 3, 31, 107] ⟨59707, 3, [(2, 1), (3, 2), (31, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_107
  · decide +kernel

theorem prime_65033 : Nat.Prime 65033 := by
  apply nodeValid_prime [2, 11, 739] ⟨65033, 3, [(2, 3), (11, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_739
  · decide +kernel

theorem prime_74017 : Nat.Prime 74017 := by
  apply nodeValid_prime [2, 3, 257] ⟨74017, 7, [(2, 5), (3, 2), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
  · decide +kernel

theorem prime_97561 : Nat.Prime 97561 := by
  apply nodeValid_prime [2, 3, 5, 271] ⟨97561, 11, [(2, 3), (3, 2), (5, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
  · decide +kernel

theorem prime_99259 : Nat.Prime 99259 := by
  apply nodeValid_prime [2, 3, 71, 233] ⟨99259, 2, [(2, 1), (3, 1), (71, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_233
  · decide +kernel

theorem prime_113189 : Nat.Prime 113189 := by
  apply nodeValid_prime [2, 28297] ⟨113189, 2, [(2, 2), (28297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28297
  · decide +kernel

theorem prime_114643 : Nat.Prime 114643 := by
  apply nodeValid_prime [2, 3, 11, 193] ⟨114643, 5, [(2, 1), (3, 3), (11, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_193
  · decide +kernel

theorem prime_132611 : Nat.Prime 132611 := by
  apply nodeValid_prime [2, 5, 89, 149] ⟨132611, 2, [(2, 1), (5, 1), (89, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_149
  · decide +kernel

theorem prime_135787 : Nat.Prime 135787 := by
  apply nodeValid_prime [2, 3, 7, 53, 61] ⟨135787, 2, [(2, 1), (3, 1), (7, 1), (53, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_61
  · decide +kernel

theorem prime_171571 : Nat.Prime 171571 := by
  apply nodeValid_prime [2, 3, 5, 7, 19, 43] ⟨171571, 10, [(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_176573 : Nat.Prime 176573 := by
  apply nodeValid_prime [2, 11, 4013] ⟨176573, 2, [(2, 2), (11, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4013
  · decide +kernel

theorem prime_184181 : Nat.Prime 184181 := by
  apply nodeValid_prime [2, 5, 9209] ⟨184181, 2, [(2, 2), (5, 1), (9209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9209
  · decide +kernel

theorem prime_214091 : Nat.Prime 214091 := by
  apply nodeValid_prime [2, 5, 79, 271] ⟨214091, 2, [(2, 1), (5, 1), (79, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_271
  · decide +kernel

theorem prime_239167 : Nat.Prime 239167 := by
  apply nodeValid_prime [2, 3, 43, 103] ⟨239167, 5, [(2, 1), (3, 3), (43, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_103
  · decide +kernel

theorem prime_241823 : Nat.Prime 241823 := by
  apply nodeValid_prime [2, 7, 23, 751] ⟨241823, 5, [(2, 1), (7, 1), (23, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_751
  · decide +kernel

theorem prime_242491 : Nat.Prime 242491 := by
  apply nodeValid_prime [2, 3, 5, 59, 137] ⟨242491, 3, [(2, 1), (3, 1), (5, 1), (59, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_137
  · decide +kernel

theorem prime_273253 : Nat.Prime 273253 := by
  apply nodeValid_prime [2, 3, 7, 3253] ⟨273253, 11, [(2, 2), (3, 1), (7, 1), (3253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3253
  · decide +kernel

theorem prime_282797 : Nat.Prime 282797 := by
  apply nodeValid_prime [2, 19, 61] ⟨282797, 2, [(2, 2), (19, 1), (61, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_284897 : Nat.Prime 284897 := by
  apply nodeValid_prime [2, 29, 307] ⟨284897, 3, [(2, 5), (29, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_307
  · decide +kernel

theorem prime_292309 : Nat.Prime 292309 := by
  apply nodeValid_prime [2, 3, 24359] ⟨292309, 2, [(2, 2), (3, 1), (24359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24359
  · decide +kernel

theorem prime_353147 : Nat.Prime 353147 := by
  apply nodeValid_prime [2, 176573] ⟨353147, 2, [(2, 1), (176573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_176573
  · decide +kernel

theorem prime_368363 : Nat.Prime 368363 := by
  apply nodeValid_prime [2, 184181] ⟨368363, 2, [(2, 1), (184181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_184181
  · decide +kernel

theorem prime_384289 : Nat.Prime 384289 := by
  apply nodeValid_prime [2, 3, 4003] ⟨384289, 14, [(2, 5), (3, 1), (4003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4003
  · decide +kernel

theorem prime_414277 : Nat.Prime 414277 := by
  apply nodeValid_prime [2, 3, 19, 23, 79] ⟨414277, 2, [(2, 2), (3, 1), (19, 1), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_423469 : Nat.Prime 423469 := by
  apply nodeValid_prime [2, 3, 1307] ⟨423469, 2, [(2, 2), (3, 4), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1307
  · decide +kernel

theorem prime_472333 : Nat.Prime 472333 := by
  apply nodeValid_prime [2, 3, 7, 5623] ⟨472333, 5, [(2, 2), (3, 1), (7, 1), (5623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5623
  · decide +kernel

theorem prime_514361 : Nat.Prime 514361 := by
  apply nodeValid_prime [2, 5, 7, 11, 167] ⟨514361, 3, [(2, 3), (5, 1), (7, 1), (11, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_167
  · decide +kernel

theorem prime_532621 : Nat.Prime 532621 := by
  apply nodeValid_prime [2, 3, 5, 11, 269] ⟨532621, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_269
  · decide +kernel

theorem prime_543287 : Nat.Prime 543287 := by
  apply nodeValid_prime [2, 17, 19, 29] ⟨543287, 5, [(2, 1), (17, 1), (19, 1), (29, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_29
  · decide +kernel

theorem prime_614051 : Nat.Prime 614051 := by
  apply nodeValid_prime [2, 5, 12281] ⟨614051, 6, [(2, 1), (5, 2), (12281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12281
  · decide +kernel

theorem prime_685361 : Nat.Prime 685361 := by
  apply nodeValid_prime [2, 5, 13, 659] ⟨685361, 3, [(2, 4), (5, 1), (13, 1), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_659
  · decide +kernel

theorem prime_1032193 : Nat.Prime 1032193 := by
  apply nodeValid_prime [2, 3, 7] ⟨1032193, 11, [(2, 14), (3, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_1094983 : Nat.Prime 1094983 := by
  apply nodeValid_prime [2, 3, 7, 29, 31] ⟨1094983, 3, [(2, 1), (3, 1), (7, 1), (29, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_31
  · decide +kernel

theorem prime_1145371 : Nat.Prime 1145371 := by
  apply nodeValid_prime [2, 3, 5, 73, 523] ⟨1145371, 2, [(2, 1), (3, 1), (5, 1), (73, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_523
  · decide +kernel

theorem prime_1330633 : Nat.Prime 1330633 := by
  apply nodeValid_prime [2, 3, 18481] ⟨1330633, 5, [(2, 3), (3, 2), (18481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18481
  · decide +kernel

theorem prime_1488121 : Nat.Prime 1488121 := by
  apply nodeValid_prime [2, 3, 5, 12401] ⟨1488121, 13, [(2, 3), (3, 1), (5, 1), (12401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12401
  · decide +kernel

theorem prime_1690081 : Nat.Prime 1690081 := by
  apply nodeValid_prime [2, 3, 5, 7, 503] ⟨1690081, 11, [(2, 5), (3, 1), (5, 1), (7, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_503
  · decide +kernel

theorem prime_1828499 : Nat.Prime 1828499 := by
  apply nodeValid_prime [2, 7, 131, 997] ⟨1828499, 2, [(2, 1), (7, 1), (131, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_997
  · decide +kernel

theorem prime_1890221 : Nat.Prime 1890221 := by
  apply nodeValid_prime [2, 5, 29, 3259] ⟨1890221, 3, [(2, 2), (5, 1), (29, 1), (3259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_3259
  · decide +kernel

theorem prime_2135641 : Nat.Prime 2135641 := by
  apply nodeValid_prime [2, 3, 5, 13, 37] ⟨2135641, 11, [(2, 3), (3, 1), (5, 1), (13, 1), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_2209189 : Nat.Prime 2209189 := by
  apply nodeValid_prime [2, 3, 47, 3917] ⟨2209189, 6, [(2, 2), (3, 1), (47, 1), (3917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_3917
  · decide +kernel

theorem prime_3395671 : Nat.Prime 3395671 := by
  apply nodeValid_prime [2, 3, 5, 113189] ⟨3395671, 11, [(2, 1), (3, 1), (5, 1), (113189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113189
  · decide +kernel

theorem prime_4376947 : Nat.Prime 4376947 := by
  apply nodeValid_prime [2, 3, 7, 23, 197] ⟨4376947, 2, [(2, 1), (3, 1), (7, 1), (23, 2), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_197
  · decide +kernel

theorem prime_4389269 : Nat.Prime 4389269 := by
  apply nodeValid_prime [2, 13, 43, 151] ⟨4389269, 2, [(2, 2), (13, 2), (43, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_151
  · decide +kernel

theorem prime_6310523 : Nat.Prime 6310523 := by
  apply nodeValid_prime [2, 59, 53479] ⟨6310523, 2, [(2, 1), (59, 1), (53479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_53479
  · decide +kernel

theorem prime_7700479 : Nat.Prime 7700479 := by
  apply nodeValid_prime [2, 3, 73, 17581] ⟨7700479, 3, [(2, 1), (3, 1), (73, 1), (17581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_17581
  · decide +kernel

theorem prime_8451631 : Nat.Prime 8451631 := by
  apply nodeValid_prime [2, 3, 5, 11, 8537] ⟨8451631, 6, [(2, 1), (3, 2), (5, 1), (11, 1), (8537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_8537
  · decide +kernel

theorem prime_8516357 : Nat.Prime 8516357 := by
  apply nodeValid_prime [2, 41, 51929] ⟨8516357, 2, [(2, 2), (41, 1), (51929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_51929
  · decide +kernel

theorem prime_8546911 : Nat.Prime 8546911 := by
  apply nodeValid_prime [2, 3, 5, 284897] ⟨8546911, 31, [(2, 1), (3, 1), (5, 1), (284897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_284897
  · decide +kernel

theorem prime_8709653 : Nat.Prime 8709653 := by
  apply nodeValid_prime [2, 7, 37, 1201] ⟨8709653, 2, [(2, 2), (7, 2), (37, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_1201
  · decide +kernel

theorem prime_9837109 : Nat.Prime 9837109 := by
  apply nodeValid_prime [2, 3, 273253] ⟨9837109, 2, [(2, 2), (3, 2), (273253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_273253
  · decide +kernel

theorem prime_15193691 : Nat.Prime 15193691 := by
  apply nodeValid_prime [2, 5, 47, 32327] ⟨15193691, 6, [(2, 1), (5, 1), (47, 1), (32327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_32327
  · decide +kernel

theorem prime_15643741 : Nat.Prime 15643741 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 313] ⟨15643741, 18, [(2, 2), (3, 1), (5, 1), (7, 2), (17, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_313
  · decide +kernel

theorem prime_15967597 : Nat.Prime 15967597 := by
  apply nodeValid_prime [2, 3, 1330633] ⟨15967597, 2, [(2, 2), (3, 1), (1330633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1330633
  · decide +kernel

theorem prime_16546393 : Nat.Prime 16546393 := by
  apply nodeValid_prime [2, 3, 79, 2909] ⟨16546393, 5, [(2, 3), (3, 2), (79, 1), (2909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_2909
  · decide +kernel

theorem prime_18868379 : Nat.Prime 18868379 := by
  apply nodeValid_prime [2, 421, 22409] ⟨18868379, 2, [(2, 1), (421, 1), (22409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_421
    · exact prime_22409
  · decide +kernel

theorem prime_24542429 : Nat.Prime 24542429 := by
  apply nodeValid_prime [2, 71, 103, 839] ⟨24542429, 2, [(2, 2), (71, 1), (103, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_103
    · exact prime_839
  · decide +kernel

theorem prime_27618211 : Nat.Prime 27618211 := by
  apply nodeValid_prime [2, 3, 5, 19, 31, 521] ⟨27618211, 11, [(2, 1), (3, 2), (5, 1), (19, 1), (31, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_31
    · exact prime_521
  · decide +kernel

theorem prime_30421459 : Nat.Prime 30421459 := by
  apply nodeValid_prime [2, 3, 1690081] ⟨30421459, 2, [(2, 1), (3, 2), (1690081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1690081
  · decide +kernel

theorem prime_30801917 : Nat.Prime 30801917 := by
  apply nodeValid_prime [2, 7700479] ⟨30801917, 2, [(2, 2), (7700479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7700479
  · decide +kernel

theorem prime_33453769 : Nat.Prime 33453769 := by
  apply nodeValid_prime [2, 3, 809, 1723] ⟨33453769, 11, [(2, 3), (3, 1), (809, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_809
    · exact prime_1723
  · decide +kernel

theorem prime_36347723 : Nat.Prime 36347723 := by
  apply nodeValid_prime [2, 19, 73, 13103] ⟨36347723, 2, [(2, 1), (19, 1), (73, 1), (13103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
    · exact prime_13103
  · decide +kernel

theorem prime_44441227 : Nat.Prime 44441227 := by
  apply nodeValid_prime [2, 3, 47, 131, 401] ⟨44441227, 2, [(2, 1), (3, 2), (47, 1), (131, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_131
    · exact prime_401
  · decide +kernel

theorem prime_46571461 : Nat.Prime 46571461 := by
  apply nodeValid_prime [2, 3, 5, 13, 59707] ⟨46571461, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (59707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_59707
  · decide +kernel

theorem prime_47233301 : Nat.Prime 47233301 := by
  apply nodeValid_prime [2, 5, 472333] ⟨47233301, 2, [(2, 2), (5, 2), (472333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_472333
  · decide +kernel

theorem prime_48519841 : Nat.Prime 48519841 := by
  apply nodeValid_prime [2, 3, 5, 271, 373] ⟨48519841, 7, [(2, 5), (3, 1), (5, 1), (271, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271
    · exact prime_373
  · decide +kernel

theorem prime_51686191 : Nat.Prime 51686191 := by
  apply nodeValid_prime [2, 3, 5, 73, 7867] ⟨51686191, 6, [(2, 1), (3, 2), (5, 1), (73, 1), (7867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_7867
  · decide +kernel

theorem prime_57400081 : Nat.Prime 57400081 := by
  apply nodeValid_prime [2, 3, 5, 239167] ⟨57400081, 17, [(2, 4), (3, 1), (5, 1), (239167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239167
  · decide +kernel

theorem prime_60167713 : Nat.Prime 60167713 := by
  apply nodeValid_prime [2, 3, 11, 227, 251] ⟨60167713, 13, [(2, 5), (3, 1), (11, 1), (227, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_227
    · exact prime_251
  · decide +kernel

theorem prime_72268879 : Nat.Prime 72268879 := by
  apply nodeValid_prime [2, 3, 11, 1094983] ⟨72268879, 3, [(2, 1), (3, 1), (11, 1), (1094983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1094983
  · decide +kernel

theorem prime_97635541 : Nat.Prime 97635541 := by
  apply nodeValid_prime [2, 3, 5, 53, 30703] ⟨97635541, 10, [(2, 2), (3, 1), (5, 1), (53, 1), (30703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
    · exact prime_30703
  · decide +kernel

theorem prime_132122329 : Nat.Prime 132122329 := by
  apply nodeValid_prime [2, 3, 13, 423469] ⟨132122329, 7, [(2, 3), (3, 1), (13, 1), (423469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_423469
  · decide +kernel

theorem prime_138231463 : Nat.Prime 138231463 := by
  apply nodeValid_prime [2, 3, 71, 131, 2477] ⟨138231463, 3, [(2, 1), (3, 1), (71, 1), (131, 1), (2477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_131
    · exact prime_2477
  · decide +kernel

theorem prime_166091473 : Nat.Prime 166091473 := by
  apply nodeValid_prime [2, 3, 42719] ⟨166091473, 13, [(2, 4), (3, 5), (42719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42719
  · decide +kernel

theorem prime_231652019 : Nat.Prime 231652019 := by
  apply nodeValid_prime [2, 13, 685361] ⟨231652019, 6, [(2, 1), (13, 2), (685361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_685361
  · decide +kernel

theorem prime_253724213 : Nat.Prime 253724213 := by
  apply nodeValid_prime [2, 7, 31, 292309] ⟨253724213, 2, [(2, 2), (7, 1), (31, 1), (292309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_292309
  · decide +kernel

theorem prime_277390643 : Nat.Prime 277390643 := by
  apply nodeValid_prime [2, 101, 251, 5471] ⟨277390643, 2, [(2, 1), (101, 1), (251, 1), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_251
    · exact prime_5471
  · decide +kernel

theorem prime_438024749 : Nat.Prime 438024749 := by
  apply nodeValid_prime [2, 7, 15643741] ⟨438024749, 2, [(2, 2), (7, 1), (15643741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15643741
  · decide +kernel

theorem prime_442144331 : Nat.Prime 442144331 := by
  apply nodeValid_prime [2, 5, 17, 107, 109, 223] ⟨442144331, 10, [(2, 1), (5, 1), (17, 1), (107, 1), (109, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_107
    · exact prime_109
    · exact prime_223
  · decide +kernel

theorem prime_487740569 : Nat.Prime 487740569 := by
  apply nodeValid_prime [2, 7, 8709653] ⟨487740569, 3, [(2, 3), (7, 1), (8709653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8709653
  · decide +kernel

theorem prime_507448427 : Nat.Prime 507448427 := by
  apply nodeValid_prime [2, 253724213] ⟨507448427, 2, [(2, 1), (253724213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_253724213
  · decide +kernel

theorem prime_552132631 : Nat.Prime 552132631 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 31, 1663] ⟨552132631, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (31, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_31
    · exact prime_1663
  · decide +kernel

theorem prime_608378521 : Nat.Prime 608378521 := by
  apply nodeValid_prime [2, 3, 5, 23, 53, 4159] ⟨608378521, 17, [(2, 3), (3, 1), (5, 1), (23, 1), (53, 1), (4159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_53
    · exact prime_4159
  · decide +kernel

theorem prime_995623913 : Nat.Prime 995623913 := by
  apply nodeValid_prime [2, 71, 233, 7523] ⟨995623913, 3, [(2, 3), (71, 1), (233, 1), (7523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_233
    · exact prime_7523
  · decide +kernel

theorem prime_1262801783 : Nat.Prime 1262801783 := by
  apply nodeValid_prime [2, 11, 57400081] ⟨1262801783, 5, [(2, 1), (11, 1), (57400081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_57400081
  · decide +kernel

theorem prime_1339526263 : Nat.Prime 1339526263 := by
  apply nodeValid_prime [2, 3, 9181, 24317] ⟨1339526263, 5, [(2, 1), (3, 1), (9181, 1), (24317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9181
    · exact prime_24317
  · decide +kernel

theorem prime_1532947049 : Nat.Prime 1532947049 := by
  apply nodeValid_prime [2, 263, 827, 881] ⟨1532947049, 3, [(2, 3), (263, 1), (827, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_827
    · exact prime_881
  · decide +kernel

theorem prime_1581915869 : Nat.Prime 1581915869 := by
  apply nodeValid_prime [2, 13, 30421459] ⟨1581915869, 2, [(2, 2), (13, 1), (30421459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_30421459
  · decide +kernel

theorem prime_1838045249 : Nat.Prime 1838045249 := by
  apply nodeValid_prime [2, 13, 2209189] ⟨1838045249, 3, [(2, 6), (13, 1), (2209189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2209189
  · decide +kernel

theorem prime_2097426041 : Nat.Prime 2097426041 := by
  apply nodeValid_prime [2, 5, 479, 109469] ⟨2097426041, 3, [(2, 3), (5, 1), (479, 1), (109469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479
    · exact prime_109469
  · decide +kernel

theorem prime_2183838199 : Nat.Prime 2183838199 := by
  apply nodeValid_prime [2, 3, 37, 9837109] ⟨2183838199, 6, [(2, 1), (3, 1), (37, 1), (9837109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_9837109
  · decide +kernel

theorem prime_3202041217 : Nat.Prime 3202041217 := by
  apply nodeValid_prime [2, 3, 11, 53, 14303] ⟨3202041217, 5, [(2, 7), (3, 1), (11, 1), (53, 1), (14303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_14303
  · decide +kernel

theorem prime_3593330413 : Nat.Prime 3593330413 := by
  apply nodeValid_prime [2, 3, 7, 3907, 10949] ⟨3593330413, 2, [(2, 2), (3, 1), (7, 1), (3907, 1), (10949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3907
    · exact prime_10949
  · decide +kernel

theorem prime_3686236747 : Nat.Prime 3686236747 := by
  apply nodeValid_prime [2, 3, 1483, 414277] ⟨3686236747, 2, [(2, 1), (3, 1), (1483, 1), (414277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1483
    · exact prime_414277
  · decide +kernel

theorem prime_6898928957 : Nat.Prime 6898928957 := by
  apply nodeValid_prime [2, 19, 61, 1488121] ⟨6898928957, 2, [(2, 2), (19, 1), (61, 1), (1488121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_61
    · exact prime_1488121
  · decide +kernel

theorem prime_15402934529 : Nat.Prime 15402934529 := by
  apply nodeValid_prime [2, 60167713] ⟨15402934529, 3, [(2, 8), (60167713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60167713
  · decide +kernel

theorem prime_136600997809 : Nat.Prime 136600997809 := by
  apply nodeValid_prime [2, 3, 11, 89, 509, 5711] ⟨136600997809, 14, [(2, 4), (3, 1), (11, 1), (89, 1), (509, 1), (5711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89
    · exact prime_509
    · exact prime_5711
  · decide +kernel

theorem prime_138860570353 : Nat.Prime 138860570353 := by
  apply nodeValid_prime [2, 3, 7, 1709, 241823] ⟨138860570353, 10, [(2, 4), (3, 1), (7, 1), (1709, 1), (241823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1709
    · exact prime_241823
  · decide +kernel

theorem prime_168640837457 : Nat.Prime 168640837457 := by
  apply nodeValid_prime [2, 7, 13, 16546393] ⟨168640837457, 3, [(2, 4), (7, 2), (13, 1), (16546393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_16546393
  · decide +kernel

theorem prime_215641083407 : Nat.Prime 215641083407 := by
  apply nodeValid_prime [2, 7, 15402934529] ⟨215641083407, 5, [(2, 1), (7, 1), (15402934529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_15402934529
  · decide +kernel

theorem prime_249520807793 : Nat.Prime 249520807793 := by
  apply nodeValid_prime [2, 17, 37, 439, 56477] ⟨249520807793, 5, [(2, 4), (17, 1), (37, 1), (439, 1), (56477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_439
    · exact prime_56477
  · decide +kernel

theorem prime_305215645069 : Nat.Prime 305215645069 := by
  apply nodeValid_prime [2, 3, 53, 311, 514361] ⟨305215645069, 6, [(2, 2), (3, 2), (53, 1), (311, 1), (514361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_311
    · exact prime_514361
  · decide +kernel

theorem prime_507768195631 : Nat.Prime 507768195631 := by
  apply nodeValid_prime [2, 3, 5, 17, 995623913] ⟨507768195631, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (995623913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_995623913
  · decide +kernel

theorem prime_508230318823 : Nat.Prime 508230318823 := by
  apply nodeValid_prime [2, 3, 3067, 27618211] ⟨508230318823, 3, [(2, 1), (3, 1), (3067, 1), (27618211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3067
    · exact prime_27618211
  · decide +kernel

theorem prime_1499866235573 : Nat.Prime 1499866235573 := by
  apply nodeValid_prime [2, 19, 58907, 335021] ⟨1499866235573, 2, [(2, 2), (19, 1), (58907, 1), (335021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_58907
    · exact prime_335021
  · decide +kernel

theorem prime_1521918999803 : Nat.Prime 1521918999803 := by
  apply nodeValid_prime [2, 751, 3583, 282797] ⟨1521918999803, 2, [(2, 1), (751, 1), (3583, 1), (282797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_751
    · exact prime_3583
    · exact prime_282797
  · decide +kernel

theorem prime_2994249693517 : Nat.Prime 2994249693517 := by
  apply nodeValid_prime [2, 3, 249520807793] ⟨2994249693517, 2, [(2, 2), (3, 1), (249520807793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_249520807793
  · decide +kernel

theorem prime_2994249696391 : Nat.Prime 2994249696391 := by
  apply nodeValid_prime [2, 3, 5, 37, 2441, 368363] ⟨2994249696391, 13, [(2, 1), (3, 2), (5, 1), (37, 1), (2441, 1), (368363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_2441
    · exact prime_368363
  · decide +kernel

theorem prime_2994249836359 : Nat.Prime 2994249836359 := by
  apply nodeValid_prime [2, 3, 11, 73, 97, 2135641] ⟨2994249836359, 3, [(2, 1), (3, 2), (11, 1), (73, 1), (97, 1), (2135641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_73
    · exact prime_97
    · exact prime_2135641
  · decide +kernel

theorem prime_2996990314957 : Nat.Prime 2996990314957 := by
  apply nodeValid_prime [2, 3, 11, 4139, 1828499] ⟨2996990314957, 2, [(2, 2), (3, 2), (11, 1), (4139, 1), (1828499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_4139
    · exact prime_1828499
  · decide +kernel

theorem prime_2996990409863 : Nat.Prime 2996990409863 := by
  apply nodeValid_prime [2, 2953, 507448427] ⟨2996990409863, 5, [(2, 1), (2953, 1), (507448427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2953
    · exact prime_507448427
  · decide +kernel

theorem prime_2996990412131 : Nat.Prime 2996990412131 := by
  apply nodeValid_prime [2, 5, 11, 13, 29, 72268879] ⟨2996990412131, 2, [(2, 1), (5, 1), (11, 1), (13, 1), (29, 1), (72268879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_29
    · exact prime_72268879
  · decide +kernel

theorem prime_2999732470753 : Nat.Prime 2999732470753 := by
  apply nodeValid_prime [2, 3, 151, 337, 614051] ⟨2999732470753, 5, [(2, 5), (3, 1), (151, 1), (337, 1), (614051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_337
    · exact prime_614051
  · decide +kernel

theorem prime_2999732471147 : Nat.Prime 2999732471147 := by
  apply nodeValid_prime [2, 1499866235573] ⟨2999732471147, 2, [(2, 1), (1499866235573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1499866235573
  · decide +kernel

theorem prime_2999732484257 : Nat.Prime 2999732484257 := by
  apply nodeValid_prime [2, 83, 103, 197, 55661] ⟨2999732484257, 3, [(2, 5), (83, 1), (103, 1), (197, 1), (55661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_103
    · exact prime_197
    · exact prime_55661
  · decide +kernel

theorem prime_3002476319363 : Nat.Prime 3002476319363 := by
  apply nodeValid_prime [2, 13, 73, 1581915869] ⟨3002476319363, 2, [(2, 1), (13, 1), (73, 1), (1581915869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
    · exact prime_1581915869
  · decide +kernel

theorem prime_3002476319833 : Nat.Prime 3002476319833 := by
  apply nodeValid_prime [2, 3, 11, 41, 277390643] ⟨3002476319833, 10, [(2, 3), (3, 1), (11, 1), (41, 1), (277390643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_277390643
  · decide +kernel

theorem prime_3002476353449 : Nat.Prime 3002476353449 := by
  apply nodeValid_prime [2, 11, 13, 101, 2753, 9439] ⟨3002476353449, 6, [(2, 3), (11, 1), (13, 1), (101, 1), (2753, 1), (9439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_101
    · exact prime_2753
    · exact prime_9439
  · decide +kernel

theorem prime_3005221911859 : Nat.Prime 3005221911859 := by
  apply nodeValid_prime [2, 3, 31, 37, 48519841] ⟨3005221911859, 2, [(2, 1), (3, 3), (31, 1), (37, 1), (48519841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_37
    · exact prime_48519841
  · decide +kernel

theorem prime_3005221951799 : Nat.Prime 3005221951799 := by
  apply nodeValid_prime [2, 11, 136600997809] ⟨3005221951799, 7, [(2, 1), (11, 1), (136600997809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_136600997809
  · decide +kernel

theorem prime_3005221951981 : Nat.Prime 3005221951981 := by
  apply nodeValid_prime [2, 3, 5, 19, 97635541] ⟨3005221951981, 10, [(2, 2), (3, 4), (5, 1), (19, 1), (97635541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_97635541
  · decide +kernel

theorem prime_3007969164373 : Nat.Prime 3007969164373 := by
  apply nodeValid_prime [2, 3, 132611, 1890221] ⟨3007969164373, 2, [(2, 2), (3, 1), (132611, 1), (1890221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_132611
    · exact prime_1890221
  · decide +kernel

theorem prime_3007969183099 : Nat.Prime 3007969183099 := by
  apply nodeValid_prime [2, 3, 11, 619, 24542429] ⟨3007969183099, 10, [(2, 1), (3, 2), (11, 1), (619, 1), (24542429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_619
    · exact prime_24542429
  · decide +kernel

theorem prime_3007969185553 : Nat.Prime 3007969185553 := by
  apply nodeValid_prime [2, 3, 17, 3686236747] ⟨3007969185553, 7, [(2, 4), (3, 1), (17, 1), (3686236747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3686236747
  · decide +kernel

theorem prime_3010718008579 : Nat.Prime 3010718008579 := by
  apply nodeValid_prime [2, 3, 7, 347, 2791, 74017] ⟨3010718008579, 2, [(2, 1), (3, 1), (7, 1), (347, 1), (2791, 1), (74017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_347
    · exact prime_2791
    · exact prime_74017
  · decide +kernel

theorem prime_3010718009527 : Nat.Prime 3010718009527 := by
  apply nodeValid_prime [2, 3, 114643, 4376947] ⟨3010718009527, 3, [(2, 1), (3, 1), (114643, 1), (4376947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_114643
    · exact prime_4376947
  · decide +kernel

theorem prime_3010718117863 : Nat.Prime 3010718117863 := by
  apply nodeValid_prime [2, 3, 7, 13, 1838045249] ⟨3010718117863, 3, [(2, 1), (3, 2), (7, 1), (13, 1), (1838045249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_1838045249
  · decide +kernel

theorem prime_3013468776229 : Nat.Prime 3013468776229 := by
  apply nodeValid_prime [2, 3, 15727, 15967597] ⟨3013468776229, 6, [(2, 2), (3, 1), (15727, 1), (15967597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15727
    · exact prime_15967597
  · decide +kernel

theorem prime_3013468810091 : Nat.Prime 3013468810091 := by
  apply nodeValid_prime [2, 5, 15971, 18868379] ⟨3013468810091, 6, [(2, 1), (5, 1), (15971, 1), (18868379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15971
    · exact prime_18868379
  · decide +kernel

theorem prime_3013468810259 : Nat.Prime 3013468810259 := by
  apply nodeValid_prime [2, 43, 30593, 1145371] ⟨3013468810259, 2, [(2, 1), (43, 1), (30593, 1), (1145371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_30593
    · exact prime_1145371
  · decide +kernel

theorem prime_3016221125977 : Nat.Prime 3016221125977 := by
  apply nodeValid_prime [2, 3, 4919, 8516357] ⟨3016221125977, 5, [(2, 3), (3, 2), (4919, 1), (8516357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4919
    · exact prime_8516357
  · decide +kernel

theorem prime_3016221149681 : Nat.Prime 3016221149681 := by
  apply nodeValid_prime [2, 5, 227, 166091473] ⟨3016221149681, 3, [(2, 4), (5, 1), (227, 1), (166091473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_227
    · exact prime_166091473
  · decide +kernel

theorem prime_3016221149939 : Nat.Prime 3016221149939 := by
  apply nodeValid_prime [2, 99259, 15193691] ⟨3016221149939, 2, [(2, 1), (99259, 1), (15193691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_99259
    · exact prime_15193691
  · decide +kernel

theorem prime_3018975151921 : Nat.Prime 3018975151921 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 138231463] ⟨3018975151921, 17, [(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (138231463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_138231463
  · decide +kernel

theorem prime_3018975152579 : Nat.Prime 3018975152579 := by
  apply nodeValid_prime [2, 7, 11, 139, 367, 384289] ⟨3018975152579, 2, [(2, 1), (7, 1), (11, 1), (139, 1), (367, 1), (384289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_139
    · exact prime_367
    · exact prime_384289
  · decide +kernel

theorem prime_3018975167699 : Nat.Prime 3018975167699 := by
  apply nodeValid_prime [2, 7, 215641083407] ⟨3018975167699, 2, [(2, 1), (7, 1), (215641083407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_215641083407
  · decide +kernel

theorem prime_3021730881601 : Nat.Prime 3021730881601 := by
  apply nodeValid_prime [2, 3, 5, 43, 397, 36877] ⟨3021730881601, 14, [(2, 6), (3, 1), (5, 2), (43, 1), (397, 1), (36877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_397
    · exact prime_36877
  · decide +kernel

theorem prime_3021730883167 : Nat.Prime 3021730883167 := by
  apply nodeValid_prime [2, 3, 73, 6898928957] ⟨3021730883167, 17, [(2, 1), (3, 1), (73, 1), (6898928957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_6898928957
  · decide +kernel

theorem prime_3021730907423 : Nat.Prime 3021730907423 := by
  apply nodeValid_prime [2, 31, 383, 3911, 32537] ⟨3021730907423, 5, [(2, 1), (31, 1), (383, 1), (3911, 1), (32537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_383
    · exact prime_3911
    · exact prime_32537
  · decide +kernel

theorem prime_3024488347753 : Nat.Prime 3024488347753 := by
  apply nodeValid_prime [2, 3, 3767, 33453769] ⟨3024488347753, 5, [(2, 3), (3, 1), (3767, 1), (33453769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3767
    · exact prime_33453769
  · decide +kernel

theorem prime_3024488348501 : Nat.Prime 3024488348501 := by
  apply nodeValid_prime [2, 5, 41, 277, 532621] ⟨3024488348501, 2, [(2, 2), (5, 3), (41, 1), (277, 1), (532621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_277
    · exact prime_532621
  · decide +kernel

theorem prime_3024488351123 : Nat.Prime 3024488351123 := by
  apply nodeValid_prime [2, 7, 103, 2097426041] ⟨3024488351123, 2, [(2, 1), (7, 1), (103, 1), (2097426041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_103
    · exact prime_2097426041
  · decide +kernel

theorem prime_3027247487843 : Nat.Prime 3027247487843 := by
  apply nodeValid_prime [2, 67, 6653, 3395671] ⟨3027247487843, 2, [(2, 1), (67, 1), (6653, 1), (3395671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_6653
    · exact prime_3395671
  · decide +kernel

theorem prime_3027247500787 : Nat.Prime 3027247500787 := by
  apply nodeValid_prime [2, 3, 11353, 44441227] ⟨3027247500787, 2, [(2, 1), (3, 1), (11353, 1), (44441227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11353
    · exact prime_44441227
  · decide +kernel

theorem prime_3027247500913 : Nat.Prime 3027247500913 := by
  apply nodeValid_prime [2, 3, 47, 157, 8546911] ⟨3027247500913, 7, [(2, 4), (3, 1), (47, 1), (157, 1), (8546911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_157
    · exact prime_8546911
  · decide +kernel

theorem prime_3030008322941 : Nat.Prime 3030008322941 := by
  apply nodeValid_prime [2, 5, 19, 67, 337, 353147] ⟨3030008322941, 3, [(2, 2), (5, 1), (19, 1), (67, 1), (337, 1), (353147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_67
    · exact prime_337
    · exact prime_353147
  · decide +kernel

theorem prime_3030008406907 : Nat.Prime 3030008406907 := by
  apply nodeValid_prime [2, 3, 13, 29, 1339526263] ⟨3030008406907, 5, [(2, 1), (3, 1), (13, 1), (29, 1), (1339526263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_1339526263
  · decide +kernel

theorem prime_3030008408521 : Nat.Prime 3030008408521 := by
  apply nodeValid_prime [2, 3, 5, 109, 231652019] ⟨3030008408521, 7, [(2, 3), (3, 1), (5, 1), (109, 1), (231652019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_231652019
  · decide +kernel

theorem prime_3032770858043 : Nat.Prime 3032770858043 := by
  apply nodeValid_prime [2, 3109, 487740569] ⟨3032770858043, 2, [(2, 1), (3109, 1), (487740569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3109
    · exact prime_487740569
  · decide +kernel

theorem prime_3032770868573 : Nat.Prime 3032770868573 := by
  apply nodeValid_prime [2, 211, 3593330413] ⟨3032770868573, 2, [(2, 2), (211, 1), (3593330413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_3593330413
  · decide +kernel

theorem prime_3032770871033 : Nat.Prime 3032770871033 := by
  apply nodeValid_prime [2, 7, 19, 163, 1571, 11131] ⟨3032770871033, 3, [(2, 3), (7, 1), (19, 1), (163, 1), (1571, 1), (11131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_163
    · exact prime_1571
    · exact prime_11131
  · decide +kernel

theorem prime_3035535073717 : Nat.Prime 3035535073717 := by
  apply nodeValid_prime [2, 3, 79, 3202041217] ⟨3035535073717, 6, [(2, 2), (3, 1), (79, 1), (3202041217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_3202041217
  · decide +kernel

theorem prime_3035535074227 : Nat.Prime 3035535074227 := by
  apply nodeValid_prime [2, 3, 168640837457] ⟨3035535074227, 2, [(2, 1), (3, 2), (168640837457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_168640837457
  · decide +kernel

theorem prime_3035535096611 : Nat.Prime 3035535096611 := by
  apply nodeValid_prime [2, 5, 139, 2183838199] ⟨3035535096611, 2, [(2, 1), (5, 1), (139, 1), (2183838199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_2183838199
  · decide +kernel

theorem prime_3038301051119 : Nat.Prime 3038301051119 := by
  apply nodeValid_prime [2, 991, 1532947049] ⟨3038301051119, 11, [(2, 1), (991, 1), (1532947049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_991
    · exact prime_1532947049
  · decide +kernel

theorem prime_3038301089899 : Nat.Prime 3038301089899 := by
  apply nodeValid_prime [2, 3, 401, 1262801783] ⟨3038301089899, 2, [(2, 1), (3, 1), (401, 1), (1262801783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_1262801783
  · decide +kernel

theorem prime_3038301092881 : Nat.Prime 3038301092881 := by
  apply nodeValid_prime [2, 3, 5, 137, 30801917] ⟨3038301092881, 7, [(2, 4), (3, 2), (5, 1), (137, 1), (30801917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_30801917
  · decide +kernel

theorem prime_3041068592519 : Nat.Prime 3041068592519 := by
  apply nodeValid_prime [2, 11, 3803, 36347723] ⟨3041068592519, 11, [(2, 1), (11, 1), (3803, 1), (36347723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3803
    · exact prime_36347723
  · decide +kernel

theorem prime_3041068593691 : Nat.Prime 3041068593691 := by
  apply nodeValid_prime [2, 3, 5, 65033, 519577] ⟨3041068593691, 2, [(2, 1), (3, 2), (5, 1), (65033, 1), (519577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_65033
    · exact prime_519577
  · decide +kernel

theorem prime_3041068708619 : Nat.Prime 3041068708619 := by
  apply nodeValid_prime [2, 19, 181, 442144331] ⟨3041068708619, 2, [(2, 1), (19, 1), (181, 1), (442144331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_181
    · exact prime_442144331
  · decide +kernel

theorem prime_3043837999607 : Nat.Prime 3043837999607 := by
  apply nodeValid_prime [2, 1521918999803] ⟨3043837999607, 5, [(2, 1), (1521918999803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1521918999803
  · decide +kernel

theorem prime_3043838001389 : Nat.Prime 3043838001389 := by
  apply nodeValid_prime [2, 179, 503, 8451631] ⟨3043838001389, 2, [(2, 2), (179, 1), (503, 1), (8451631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_503
    · exact prime_8451631
  · decide +kernel

theorem prime_3043838066473 : Nat.Prime 3043838066473 := by
  apply nodeValid_prime [2, 3, 7, 5851, 1032193] ⟨3043838066473, 15, [(2, 3), (3, 2), (7, 1), (5851, 1), (1032193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5851
    · exact prime_1032193
  · decide +kernel

theorem prime_3046609130041 : Nat.Prime 3046609130041 := by
  apply nodeValid_prime [2, 3, 5, 7, 5647, 214091] ⟨3046609130041, 19, [(2, 3), (3, 2), (5, 1), (7, 1), (5647, 1), (214091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_5647
    · exact prime_214091
  · decide +kernel

theorem prime_3046609169977 : Nat.Prime 3046609169977 := by
  apply nodeValid_prime [2, 3, 28921, 4389269] ⟨3046609169977, 5, [(2, 3), (3, 1), (28921, 1), (4389269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28921
    · exact prime_4389269
  · decide +kernel

theorem prime_3046609173787 : Nat.Prime 3046609173787 := by
  apply nodeValid_prime [2, 3, 507768195631] ⟨3046609173787, 2, [(2, 1), (3, 1), (507768195631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_507768195631
  · decide +kernel

theorem prime_3049381896619 : Nat.Prime 3049381896619 := by
  apply nodeValid_prime [2, 3, 9833, 51686191] ⟨3049381896619, 7, [(2, 1), (3, 1), (9833, 1), (51686191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9833
    · exact prime_51686191
  · decide +kernel

theorem prime_3049381912561 : Nat.Prime 3049381912561 := by
  apply nodeValid_prime [2, 3, 5, 269, 47233301] ⟨3049381912561, 11, [(2, 4), (3, 1), (5, 1), (269, 1), (47233301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_269
    · exact prime_47233301
  · decide +kernel

theorem prime_3049381912939 : Nat.Prime 3049381912939 := by
  apply nodeValid_prime [2, 3, 508230318823] ⟨3049381912939, 2, [(2, 1), (3, 1), (508230318823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_508230318823
  · decide +kernel

theorem prime_3052156366111 : Nat.Prime 3052156366111 := by
  apply nodeValid_prime [2, 3, 5, 683, 1097, 135787] ⟨3052156366111, 3, [(2, 1), (3, 1), (5, 1), (683, 1), (1097, 1), (135787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_683
    · exact prime_1097
    · exact prime_135787
  · decide +kernel

theorem prime_3052156450691 : Nat.Prime 3052156450691 := by
  apply nodeValid_prime [2, 5, 305215645069] ⟨3052156450691, 2, [(2, 1), (5, 1), (305215645069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_305215645069
  · decide +kernel

theorem prime_3052156451033 : Nat.Prime 3052156451033 := by
  apply nodeValid_prime [2, 13, 67, 438024749] ⟨3052156451033, 5, [(2, 3), (13, 1), (67, 1), (438024749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_438024749
  · decide +kernel

theorem prime_3054932489867 : Nat.Prime 3054932489867 := by
  apply nodeValid_prime [2, 2341, 3803, 171571] ⟨3054932489867, 2, [(2, 1), (2341, 1), (3803, 1), (171571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2341
    · exact prime_3803
    · exact prime_171571
  · decide +kernel

theorem prime_3054932491139 : Nat.Prime 3054932491139 := by
  apply nodeValid_prime [2, 11, 1051, 132122329] ⟨3054932491139, 2, [(2, 1), (11, 1), (1051, 1), (132122329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1051
    · exact prime_132122329
  · decide +kernel

theorem prime_3054932547767 : Nat.Prime 3054932547767 := by
  apply nodeValid_prime [2, 11, 138860570353] ⟨3054932547767, 5, [(2, 1), (11, 1), (138860570353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_138860570353
  · decide +kernel

theorem prime_3057710446547 : Nat.Prime 3057710446547 := by
  apply nodeValid_prime [2, 7, 359, 608378521] ⟨3057710446547, 2, [(2, 1), (7, 1), (359, 1), (608378521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_359
    · exact prime_608378521
  · decide +kernel

theorem prime_3057710508217 : Nat.Prime 3057710508217 := by
  apply nodeValid_prime [2, 3, 7, 13, 859, 543287] ⟨3057710508217, 5, [(2, 3), (3, 2), (7, 1), (13, 1), (859, 1), (543287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_859
    · exact prime_543287
  · decide +kernel

theorem prime_3057710510479 : Nat.Prime 3057710510479 := by
  apply nodeValid_prime [2, 3, 13, 71, 552132631] ⟨3057710510479, 7, [(2, 1), (3, 1), (13, 1), (71, 1), (552132631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_552132631
  · decide +kernel

theorem prime_3060490065587 : Nat.Prime 3060490065587 := by
  apply nodeValid_prime [2, 242491, 6310523] ⟨3060490065587, 2, [(2, 1), (242491, 1), (6310523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_242491
    · exact prime_6310523
  · decide +kernel

theorem prime_3060490130977 : Nat.Prime 3060490130977 := by
  apply nodeValid_prime [2, 3, 31, 83, 127, 97561] ⟨3060490130977, 5, [(2, 5), (3, 1), (31, 1), (83, 1), (127, 1), (97561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_83
    · exact prime_127
    · exact prime_97561
  · decide +kernel

theorem prime_3060490131077 : Nat.Prime 3060490131077 := by
  apply nodeValid_prime [2, 7, 2347, 46571461] ⟨3060490131077, 3, [(2, 2), (7, 1), (2347, 1), (46571461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2347
    · exact prime_46571461
  · decide +kernel

end Sude.Lucas.Generated
