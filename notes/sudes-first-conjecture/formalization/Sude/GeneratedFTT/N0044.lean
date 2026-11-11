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
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3389 : Nat.Prime 3389 := by
  apply nodeValid_prime [2, 7, 11] ⟨3389, 3, [(2, 2), (7, 1), (11, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_6779 : Nat.Prime 6779 := by
  apply nodeValid_prime [2, 3389] ⟨6779, 2, [(2, 1), (3389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3389
  · decide +kernel

theorem prime_7229 : Nat.Prime 7229 := by
  apply nodeValid_prime [2, 13, 139] ⟨7229, 2, [(2, 2), (13, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_139
  · decide +kernel

theorem prime_7603 : Nat.Prime 7603 := by
  apply nodeValid_prime [2, 3, 7, 181] ⟨7603, 2, [(2, 1), (3, 1), (7, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_181
  · decide +kernel

theorem prime_8677 : Nat.Prime 8677 := by
  apply nodeValid_prime [2, 3, 241] ⟨8677, 2, [(2, 2), (3, 2), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel

theorem prime_9613 : Nat.Prime 9613 := by
  apply nodeValid_prime [2, 3, 89] ⟨9613, 2, [(2, 2), (3, 3), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_9787 : Nat.Prime 9787 := by
  apply nodeValid_prime [2, 3, 7, 233] ⟨9787, 3, [(2, 1), (3, 1), (7, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_233
  · decide +kernel

theorem prime_11519 : Nat.Prime 11519 := by
  apply nodeValid_prime [2, 13, 443] ⟨11519, 7, [(2, 1), (13, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_443
  · decide +kernel

theorem prime_12577 : Nat.Prime 12577 := by
  apply nodeValid_prime [2, 3, 131] ⟨12577, 10, [(2, 5), (3, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_14083 : Nat.Prime 14083 := by
  apply nodeValid_prime [2, 3, 2347] ⟨14083, 3, [(2, 1), (3, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2347
  · decide +kernel

theorem prime_18433 : Nat.Prime 18433 := by
  apply nodeValid_prime [2, 3] ⟨18433, 5, [(2, 11), (3, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_19213 : Nat.Prime 19213 := by
  apply nodeValid_prime [2, 3, 1601] ⟨19213, 5, [(2, 2), (3, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1601
  · decide +kernel

theorem prime_20773 : Nat.Prime 20773 := by
  apply nodeValid_prime [2, 3, 577] ⟨20773, 2, [(2, 2), (3, 2), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_577
  · decide +kernel

theorem prime_20921 : Nat.Prime 20921 := by
  apply nodeValid_prime [2, 5, 523] ⟨20921, 3, [(2, 3), (5, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_523
  · decide +kernel

theorem prime_24373 : Nat.Prime 24373 := by
  apply nodeValid_prime [2, 3, 677] ⟨24373, 7, [(2, 2), (3, 2), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
  · decide +kernel

theorem prime_26111 : Nat.Prime 26111 := by
  apply nodeValid_prime [2, 5, 7, 373] ⟨26111, 7, [(2, 1), (5, 1), (7, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_373
  · decide +kernel

theorem prime_26951 : Nat.Prime 26951 := by
  apply nodeValid_prime [2, 5, 7, 11] ⟨26951, 7, [(2, 1), (5, 2), (7, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_30241 : Nat.Prime 30241 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨30241, 11, [(2, 5), (3, 3), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_38153 : Nat.Prime 38153 := by
  apply nodeValid_prime [2, 19, 251] ⟨38153, 3, [(2, 3), (19, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_251
  · decide +kernel

theorem prime_39079 : Nat.Prime 39079 := by
  apply nodeValid_prime [2, 3, 13, 167] ⟨39079, 3, [(2, 1), (3, 2), (13, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_167
  · decide +kernel

theorem prime_39233 : Nat.Prime 39233 := by
  apply nodeValid_prime [2, 613] ⟨39233, 3, [(2, 6), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_613
  · decide +kernel

theorem prime_39821 : Nat.Prime 39821 := by
  apply nodeValid_prime [2, 5, 11, 181] ⟨39821, 2, [(2, 2), (5, 1), (11, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_181
  · decide +kernel

theorem prime_41521 : Nat.Prime 41521 := by
  apply nodeValid_prime [2, 3, 5, 173] ⟨41521, 22, [(2, 4), (3, 1), (5, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
  · decide +kernel

theorem prime_41669 : Nat.Prime 41669 := by
  apply nodeValid_prime [2, 11, 947] ⟨41669, 2, [(2, 2), (11, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_947
  · decide +kernel

theorem prime_41843 : Nat.Prime 41843 := by
  apply nodeValid_prime [2, 20921] ⟨41843, 2, [(2, 1), (20921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20921
  · decide +kernel

theorem prime_43961 : Nat.Prime 43961 := by
  apply nodeValid_prime [2, 5, 7, 157] ⟨43961, 6, [(2, 3), (5, 1), (7, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_157
  · decide +kernel

theorem prime_52223 : Nat.Prime 52223 := by
  apply nodeValid_prime [2, 26111] ⟨52223, 5, [(2, 1), (26111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26111
  · decide +kernel

theorem prime_53611 : Nat.Prime 53611 := by
  apply nodeValid_prime [2, 3, 5, 1787] ⟨53611, 10, [(2, 1), (3, 1), (5, 1), (1787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1787
  · decide +kernel

theorem prime_57097 : Nat.Prime 57097 := by
  apply nodeValid_prime [2, 3, 13, 61] ⟨57097, 7, [(2, 3), (3, 2), (13, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_61
  · decide +kernel

theorem prime_57559 : Nat.Prime 57559 := by
  apply nodeValid_prime [2, 3, 53, 181] ⟨57559, 6, [(2, 1), (3, 1), (53, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_181
  · decide +kernel

theorem prime_59021 : Nat.Prime 59021 := by
  apply nodeValid_prime [2, 5, 13, 227] ⟨59021, 2, [(2, 2), (5, 1), (13, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_227
  · decide +kernel

theorem prime_61717 : Nat.Prime 61717 := by
  apply nodeValid_prime [2, 3, 37, 139] ⟨61717, 2, [(2, 2), (3, 1), (37, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_139
  · decide +kernel

theorem prime_75821 : Nat.Prime 75821 := by
  apply nodeValid_prime [2, 5, 17, 223] ⟨75821, 2, [(2, 2), (5, 1), (17, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_223
  · decide +kernel

theorem prime_76031 : Nat.Prime 76031 := by
  apply nodeValid_prime [2, 5, 7603] ⟨76031, 7, [(2, 1), (5, 1), (7603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7603
  · decide +kernel

theorem prime_79609 : Nat.Prime 79609 := by
  apply nodeValid_prime [2, 3, 31, 107] ⟨79609, 14, [(2, 3), (3, 1), (31, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_107
  · decide +kernel

theorem prime_83093 : Nat.Prime 83093 := by
  apply nodeValid_prime [2, 20773] ⟨83093, 2, [(2, 2), (20773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20773
  · decide +kernel

theorem prime_88969 : Nat.Prime 88969 := by
  apply nodeValid_prime [2, 3, 11, 337] ⟨88969, 7, [(2, 3), (3, 1), (11, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_337
  · decide +kernel

theorem prime_114889 : Nat.Prime 114889 := by
  apply nodeValid_prime [2, 3, 4787] ⟨114889, 13, [(2, 3), (3, 1), (4787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4787
  · decide +kernel

theorem prime_119627 : Nat.Prime 119627 := by
  apply nodeValid_prime [2, 13, 43, 107] ⟨119627, 2, [(2, 1), (13, 1), (43, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_43
    · exact prime_107
  · decide +kernel

theorem prime_127321 : Nat.Prime 127321 := by
  apply nodeValid_prime [2, 3, 5, 1061] ⟨127321, 11, [(2, 3), (3, 1), (5, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1061
  · decide +kernel

theorem prime_130547 : Nat.Prime 130547 := by
  apply nodeValid_prime [2, 13, 5021] ⟨130547, 2, [(2, 1), (13, 1), (5021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5021
  · decide +kernel

theorem prime_138497 : Nat.Prime 138497 := by
  apply nodeValid_prime [2, 541] ⟨138497, 3, [(2, 8), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_541
  · decide +kernel

theorem prime_151643 : Nat.Prime 151643 := by
  apply nodeValid_prime [2, 75821] ⟨151643, 2, [(2, 1), (75821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_75821
  · decide +kernel

theorem prime_152063 : Nat.Prime 152063 := by
  apply nodeValid_prime [2, 76031] ⟨152063, 5, [(2, 1), (76031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76031
  · decide +kernel

theorem prime_185477 : Nat.Prime 185477 := by
  apply nodeValid_prime [2, 89, 521] ⟨185477, 2, [(2, 2), (89, 1), (521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_521
  · decide +kernel

theorem prime_200363 : Nat.Prime 200363 := by
  apply nodeValid_prime [2, 17, 71, 83] ⟨200363, 2, [(2, 1), (17, 1), (71, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_71
    · exact prime_83
  · decide +kernel

theorem prime_216901 : Nat.Prime 216901 := by
  apply nodeValid_prime [2, 3, 5, 241] ⟨216901, 2, [(2, 2), (3, 2), (5, 2), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_240173 : Nat.Prime 240173 := by
  apply nodeValid_prime [2, 97, 619] ⟨240173, 2, [(2, 2), (97, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_619
  · decide +kernel

theorem prime_251527 : Nat.Prime 251527 := by
  apply nodeValid_prime [2, 3, 11, 37, 103] ⟨251527, 3, [(2, 1), (3, 1), (11, 1), (37, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_103
  · decide +kernel

theorem prime_253811 : Nat.Prime 253811 := by
  apply nodeValid_prime [2, 5, 17, 1493] ⟨253811, 2, [(2, 1), (5, 1), (17, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1493
  · decide +kernel

theorem prime_302411 : Nat.Prime 302411 := by
  apply nodeValid_prime [2, 5, 30241] ⟨302411, 6, [(2, 1), (5, 1), (30241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_30241
  · decide +kernel

theorem prime_303287 : Nat.Prime 303287 := by
  apply nodeValid_prime [2, 151643] ⟨303287, 5, [(2, 1), (151643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_151643
  · decide +kernel

theorem prime_304039 : Nat.Prime 304039 := by
  apply nodeValid_prime [2, 3, 7, 19, 127] ⟨304039, 3, [(2, 1), (3, 2), (7, 1), (19, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_127
  · decide +kernel

theorem prime_318569 : Nat.Prime 318569 := by
  apply nodeValid_prime [2, 39821] ⟨318569, 3, [(2, 3), (39821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39821
  · decide +kernel

theorem prime_361961 : Nat.Prime 361961 := by
  apply nodeValid_prime [2, 5, 9049] ⟨361961, 6, [(2, 3), (5, 1), (9049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9049
  · decide +kernel

theorem prime_371237 : Nat.Prime 371237 := by
  apply nodeValid_prime [2, 92809] ⟨371237, 2, [(2, 2), (92809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92809
  · decide +kernel

theorem prime_394393 : Nat.Prime 394393 := by
  apply nodeValid_prime [2, 3, 16433] ⟨394393, 5, [(2, 3), (3, 1), (16433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16433
  · decide +kernel

theorem prime_438211 : Nat.Prime 438211 := by
  apply nodeValid_prime [2, 3, 5, 541] ⟨438211, 2, [(2, 1), (3, 4), (5, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_541
  · decide +kernel

theorem prime_457837 : Nat.Prime 457837 := by
  apply nodeValid_prime [2, 3, 38153] ⟨457837, 2, [(2, 2), (3, 1), (38153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_38153
  · decide +kernel

theorem prime_495437 : Nat.Prime 495437 := by
  apply nodeValid_prime [2, 29, 4271] ⟨495437, 2, [(2, 2), (29, 1), (4271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_4271
  · decide +kernel

theorem prime_570959 : Nat.Prime 570959 := by
  apply nodeValid_prime [2, 31, 9209] ⟨570959, 7, [(2, 1), (31, 1), (9209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_9209
  · decide +kernel

theorem prime_601219 : Nat.Prime 601219 := by
  apply nodeValid_prime [2, 3, 127, 263] ⟨601219, 2, [(2, 1), (3, 2), (127, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_263
  · decide +kernel

theorem prime_604823 : Nat.Prime 604823 := by
  apply nodeValid_prime [2, 302411] ⟨604823, 5, [(2, 1), (302411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_302411
  · decide +kernel

theorem prime_723923 : Nat.Prime 723923 := by
  apply nodeValid_prime [2, 361961] ⟨723923, 2, [(2, 1), (361961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_361961
  · decide +kernel

theorem prime_730589 : Nat.Prime 730589 := by
  apply nodeValid_prime [2, 19, 9613] ⟨730589, 2, [(2, 2), (19, 1), (9613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_9613
  · decide +kernel

theorem prime_763927 : Nat.Prime 763927 := by
  apply nodeValid_prime [2, 3, 127321] ⟨763927, 3, [(2, 1), (3, 1), (127321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127321
  · decide +kernel

theorem prime_796091 : Nat.Prime 796091 := by
  apply nodeValid_prime [2, 5, 79609] ⟨796091, 7, [(2, 1), (5, 1), (79609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79609
  · decide +kernel

theorem prime_812137 : Nat.Prime 812137 := by
  apply nodeValid_prime [2, 3, 13, 19, 137] ⟨812137, 5, [(2, 3), (3, 1), (13, 1), (19, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_137
  · decide +kernel

theorem prime_838949 : Nat.Prime 838949 := by
  apply nodeValid_prime [2, 11, 23, 829] ⟨838949, 2, [(2, 2), (11, 1), (23, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_829
  · decide +kernel

theorem prime_1004233 : Nat.Prime 1004233 := by
  apply nodeValid_prime [2, 3, 41843] ⟨1004233, 7, [(2, 3), (3, 1), (41843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41843
  · decide +kernel

theorem prime_1033451 : Nat.Prime 1033451 := by
  apply nodeValid_prime [2, 5, 11, 1879] ⟨1033451, 2, [(2, 1), (5, 2), (11, 1), (1879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1879
  · decide +kernel

theorem prime_1209647 : Nat.Prime 1209647 := by
  apply nodeValid_prime [2, 604823] ⟨1209647, 5, [(2, 1), (604823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_604823
  · decide +kernel

theorem prime_1234721 : Nat.Prime 1234721 := by
  apply nodeValid_prime [2, 5, 7717] ⟨1234721, 3, [(2, 5), (5, 1), (7717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7717
  · decide +kernel

theorem prime_1378669 : Nat.Prime 1378669 := by
  apply nodeValid_prime [2, 3, 114889] ⟨1378669, 2, [(2, 2), (3, 1), (114889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_114889
  · decide +kernel

theorem prime_1577573 : Nat.Prime 1577573 := by
  apply nodeValid_prime [2, 394393] ⟨1577573, 2, [(2, 2), (394393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_394393
  · decide +kernel

theorem prime_1677899 : Nat.Prime 1677899 := by
  apply nodeValid_prime [2, 838949] ⟨1677899, 2, [(2, 1), (838949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_838949
  · decide +kernel

theorem prime_1901839 : Nat.Prime 1901839 := by
  apply nodeValid_prime [2, 3, 197, 1609] ⟨1901839, 3, [(2, 1), (3, 1), (197, 1), (1609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1609
  · decide +kernel

theorem prime_1946501 : Nat.Prime 1946501 := by
  apply nodeValid_prime [2, 5, 17, 229] ⟨1946501, 2, [(2, 2), (5, 3), (17, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_229
  · decide +kernel

theorem prime_2286793 : Nat.Prime 2286793 := by
  apply nodeValid_prime [2, 3, 3529] ⟨2286793, 7, [(2, 3), (3, 4), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3529
  · decide +kernel

theorem prime_2895647 : Nat.Prime 2895647 := by
  apply nodeValid_prime [2, 13, 659] ⟨2895647, 5, [(2, 1), (13, 3), (659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_659
  · decide +kernel

theorem prime_2974451 : Nat.Prime 2974451 := by
  apply nodeValid_prime [2, 5, 19, 31, 101] ⟨2974451, 6, [(2, 1), (5, 2), (19, 1), (31, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_31
    · exact prime_101
  · decide +kernel

theorem prime_3053231 : Nat.Prime 3053231 := by
  apply nodeValid_prime [2, 5, 101, 3023] ⟨3053231, 11, [(2, 1), (5, 1), (101, 1), (3023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_101
    · exact prime_3023
  · decide +kernel

theorem prime_3149753 : Nat.Prime 3149753 := by
  apply nodeValid_prime [2, 47, 8377] ⟨3149753, 3, [(2, 3), (47, 1), (8377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_8377
  · decide +kernel

theorem prime_3155147 : Nat.Prime 3155147 := by
  apply nodeValid_prime [2, 1577573] ⟨3155147, 2, [(2, 1), (1577573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1577573
  · decide +kernel

theorem prime_3288023 : Nat.Prime 3288023 := by
  apply nodeValid_prime [2, 61, 26951] ⟨3288023, 5, [(2, 1), (61, 1), (26951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_26951
  · decide +kernel

theorem prime_4214087 : Nat.Prime 4214087 := by
  apply nodeValid_prime [2, 19, 43, 2579] ⟨4214087, 5, [(2, 1), (19, 1), (43, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_2579
  · decide +kernel

theorem prime_4952081 : Nat.Prime 4952081 := by
  apply nodeValid_prime [2, 5, 7, 37, 239] ⟨4952081, 6, [(2, 4), (5, 1), (7, 1), (37, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_239
  · decide +kernel

theorem prime_5076221 : Nat.Prime 5076221 := by
  apply nodeValid_prime [2, 5, 253811] ⟨5076221, 3, [(2, 2), (5, 1), (253811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_253811
  · decide +kernel

theorem prime_5363243 : Nat.Prime 5363243 := by
  apply nodeValid_prime [2, 61, 43961] ⟨5363243, 2, [(2, 1), (61, 1), (43961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_43961
  · decide +kernel

theorem prime_5648197 : Nat.Prime 5648197 := by
  apply nodeValid_prime [2, 3, 131, 3593] ⟨5648197, 5, [(2, 2), (3, 1), (131, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_3593
  · decide +kernel

theorem prime_5734243 : Nat.Prime 5734243 := by
  apply nodeValid_prime [2, 3, 318569] ⟨5734243, 7, [(2, 1), (3, 2), (318569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_318569
  · decide +kernel

theorem prime_7639271 : Nat.Prime 7639271 := by
  apply nodeValid_prime [2, 5, 763927] ⟨7639271, 19, [(2, 1), (5, 1), (763927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_763927
  · decide +kernel

theorem prime_7649641 : Nat.Prime 7649641 := by
  apply nodeValid_prime [2, 3, 5, 787] ⟨7649641, 7, [(2, 3), (3, 5), (5, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_787
  · decide +kernel

theorem prime_7664407 : Nat.Prime 7664407 := by
  apply nodeValid_prime [2, 3, 43, 61, 487] ⟨7664407, 5, [(2, 1), (3, 1), (43, 1), (61, 1), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_61
    · exact prime_487
  · decide +kernel

theorem prime_8211403 : Nat.Prime 8211403 := by
  apply nodeValid_prime [2, 3, 152063] ⟨8211403, 3, [(2, 1), (3, 3), (152063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_152063
  · decide +kernel

theorem prime_9490601 : Nat.Prime 9490601 := by
  apply nodeValid_prime [2, 5, 7, 6779] ⟨9490601, 3, [(2, 3), (5, 2), (7, 1), (6779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6779
  · decide +kernel

theorem prime_10094593 : Nat.Prime 10094593 := by
  apply nodeValid_prime [2, 3, 31, 53] ⟨10094593, 5, [(2, 11), (3, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_11679007 : Nat.Prime 11679007 := by
  apply nodeValid_prime [2, 3, 1946501] ⟨11679007, 3, [(2, 1), (3, 1), (1946501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1946501
  · decide +kernel

theorem prime_15560249 : Nat.Prime 15560249 := by
  apply nodeValid_prime [2, 11, 151, 1171] ⟨15560249, 3, [(2, 3), (11, 1), (151, 1), (1171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_151
    · exact prime_1171
  · decide +kernel

theorem prime_16648991 : Nat.Prime 16648991 := by
  apply nodeValid_prime [2, 5, 887, 1877] ⟨16648991, 7, [(2, 1), (5, 1), (887, 1), (1877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_887
    · exact prime_1877
  · decide +kernel

theorem prime_18449237 : Nat.Prime 18449237 := by
  apply nodeValid_prime [2, 13, 37, 43, 223] ⟨18449237, 2, [(2, 2), (13, 1), (37, 1), (43, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_37
    · exact prime_43
    · exact prime_223
  · decide +kernel

theorem prime_28939811 : Nat.Prime 28939811 := by
  apply nodeValid_prime [2, 5, 157, 18433] ⟨28939811, 2, [(2, 1), (5, 1), (157, 1), (18433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_18433
  · decide +kernel

theorem prime_30657629 : Nat.Prime 30657629 := by
  apply nodeValid_prime [2, 7664407] ⟨30657629, 2, [(2, 2), (7664407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7664407
  · decide +kernel

theorem prime_54883033 : Nat.Prime 54883033 := by
  apply nodeValid_prime [2, 3, 2286793] ⟨54883033, 5, [(2, 3), (3, 1), (2286793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2286793
  · decide +kernel

theorem prime_66196279 : Nat.Prime 66196279 := by
  apply nodeValid_prime [2, 3, 401, 1019] ⟨66196279, 3, [(2, 1), (3, 4), (401, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_401
    · exact prime_1019
  · decide +kernel

theorem prime_75085403 : Nat.Prime 75085403 := by
  apply nodeValid_prime [2, 7, 5363243] ⟨75085403, 2, [(2, 1), (7, 1), (5363243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5363243
  · decide +kernel

theorem prime_85037159 : Nat.Prime 85037159 := by
  apply nodeValid_prime [2, 307, 138497] ⟨85037159, 7, [(2, 1), (307, 1), (138497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_138497
  · decide +kernel

theorem prime_91371979 : Nat.Prime 91371979 := by
  apply nodeValid_prime [2, 3, 5076221] ⟨91371979, 3, [(2, 1), (3, 2), (5076221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5076221
  · decide +kernel

theorem prime_123487181 : Nat.Prime 123487181 := by
  apply nodeValid_prime [2, 5, 61, 127, 797] ⟨123487181, 2, [(2, 2), (5, 1), (61, 1), (127, 1), (797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_127
    · exact prime_797
  · decide +kernel

theorem prime_131132297 : Nat.Prime 131132297 := by
  apply nodeValid_prime [2, 1423, 11519] ⟨131132297, 3, [(2, 3), (1423, 1), (11519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1423
    · exact prime_11519
  · decide +kernel

theorem prime_140319911 : Nat.Prime 140319911 := by
  apply nodeValid_prime [2, 5, 37, 47, 8069] ⟨140319911, 7, [(2, 1), (5, 1), (37, 1), (47, 1), (8069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_47
    · exact prime_8069
  · decide +kernel

theorem prime_152785421 : Nat.Prime 152785421 := by
  apply nodeValid_prime [2, 5, 7639271] ⟨152785421, 2, [(2, 2), (5, 1), (7639271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7639271
  · decide +kernel

theorem prime_186864113 : Nat.Prime 186864113 := by
  apply nodeValid_prime [2, 11679007] ⟨186864113, 3, [(2, 4), (11679007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11679007
  · decide +kernel

theorem prime_258349591 : Nat.Prime 258349591 := by
  apply nodeValid_prime [2, 3, 5, 43, 241, 277] ⟨258349591, 11, [(2, 1), (3, 2), (5, 1), (43, 1), (241, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_241
    · exact prime_277
  · decide +kernel

theorem prime_665867329 : Nat.Prime 665867329 := by
  apply nodeValid_prime [2, 3, 7, 495437] ⟨665867329, 11, [(2, 6), (3, 1), (7, 1), (495437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_495437
  · decide +kernel

theorem prime_771184987 : Nat.Prime 771184987 := by
  apply nodeValid_prime [2, 3, 11, 13, 23, 39079] ⟨771184987, 3, [(2, 1), (3, 1), (11, 1), (13, 1), (23, 1), (39079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_39079
  · decide +kernel

theorem prime_786793783 : Nat.Prime 786793783 := by
  apply nodeValid_prime [2, 3, 131132297] ⟨786793783, 6, [(2, 1), (3, 1), (131132297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131132297
  · decide +kernel

theorem prime_818814713 : Nat.Prime 818814713 := by
  apply nodeValid_prime [2, 61, 1677899] ⟨818814713, 3, [(2, 3), (61, 1), (1677899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_1677899
  · decide +kernel

theorem prime_1048142027 : Nat.Prime 1048142027 := by
  apply nodeValid_prime [2, 12577, 41669] ⟨1048142027, 2, [(2, 1), (12577, 1), (41669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_12577
    · exact prime_41669
  · decide +kernel

theorem prime_1681416553 : Nat.Prime 1681416553 := by
  apply nodeValid_prime [2, 3, 17, 19, 216901] ⟨1681416553, 7, [(2, 3), (3, 1), (17, 1), (19, 1), (216901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_216901
  · decide +kernel

theorem prime_1791560761 : Nat.Prime 1791560761 := by
  apply nodeValid_prime [2, 3, 5, 11, 113, 12011] ⟨1791560761, 19, [(2, 3), (3, 1), (5, 1), (11, 1), (113, 1), (12011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_113
    · exact prime_12011
  · decide +kernel

theorem prime_3177421393 : Nat.Prime 3177421393 := by
  apply nodeValid_prime [2, 3, 66196279] ⟨3177421393, 15, [(2, 4), (3, 1), (66196279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66196279
  · decide +kernel

theorem prime_6559974191 : Nat.Prime 6559974191 := by
  apply nodeValid_prime [2, 5, 7, 11, 107, 79621] ⟨6559974191, 7, [(2, 1), (5, 1), (7, 1), (11, 1), (107, 1), (79621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_107
    · exact prime_79621
  · decide +kernel

theorem prime_8385136217 : Nat.Prime 8385136217 := by
  apply nodeValid_prime [2, 1048142027] ⟨8385136217, 3, [(2, 3), (1048142027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1048142027
  · decide +kernel

theorem prime_9733700429 : Nat.Prime 9733700429 := by
  apply nodeValid_prime [2, 797, 3053231] ⟨9733700429, 2, [(2, 2), (797, 1), (3053231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_797
    · exact prime_3053231
  · decide +kernel

theorem prime_12202593563 : Nat.Prime 12202593563 := by
  apply nodeValid_prime [2, 37, 137, 317, 3797] ⟨12202593563, 2, [(2, 1), (37, 1), (137, 1), (317, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_137
    · exact prime_317
    · exact prime_3797
  · decide +kernel

theorem prime_13119948383 : Nat.Prime 13119948383 := by
  apply nodeValid_prime [2, 6559974191] ⟨13119948383, 5, [(2, 1), (6559974191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6559974191
  · decide +kernel

theorem prime_15876923731 : Nat.Prime 15876923731 := by
  apply nodeValid_prime [2, 3, 5, 17, 31, 1004233] ⟨15876923731, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (31, 1), (1004233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_1004233
  · decide +kernel

theorem prime_26967626951 : Nat.Prime 26967626951 := by
  apply nodeValid_prime [2, 5, 11, 31, 53, 2713] ⟨26967626951, 11, [(2, 1), (5, 2), (11, 2), (31, 1), (53, 1), (2713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_53
    · exact prime_2713
  · decide +kernel

theorem prime_35956835767 : Nat.Prime 35956835767 := by
  apply nodeValid_prime [2, 3, 665867329] ⟨35956835767, 3, [(2, 1), (3, 3), (665867329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_665867329
  · decide +kernel

theorem prime_36991164167 : Nat.Prime 36991164167 := by
  apply nodeValid_prime [2, 11, 1681416553] ⟨36991164167, 10, [(2, 1), (11, 1), (1681416553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1681416553
  · decide +kernel

theorem prime_53935253903 : Nat.Prime 53935253903 := by
  apply nodeValid_prime [2, 26967626951] ⟨53935253903, 5, [(2, 1), (26967626951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26967626951
  · decide +kernel

theorem prime_64431595171 : Nat.Prime 64431595171 := by
  apply nodeValid_prime [2, 3, 5, 43, 16648991] ⟨64431595171, 2, [(2, 1), (3, 2), (5, 1), (43, 1), (16648991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_16648991
  · decide +kernel

theorem prime_65111285329 : Nat.Prime 65111285329 := by
  apply nodeValid_prime [2, 3, 5393, 251527] ⟨65111285329, 7, [(2, 4), (3, 1), (5393, 1), (251527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5393
    · exact prime_251527
  · decide +kernel

theorem prime_66287748001 : Nat.Prime 66287748001 := by
  apply nodeValid_prime [2, 3, 5, 23, 240173] ⟨66287748001, 11, [(2, 5), (3, 1), (5, 3), (23, 1), (240173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_240173
  · decide +kernel

theorem prime_108032327363 : Nat.Prime 108032327363 := by
  apply nodeValid_prime [2, 17, 3177421393] ⟨108032327363, 2, [(2, 1), (17, 1), (3177421393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3177421393
  · decide +kernel

theorem prime_164244332233 : Nat.Prime 164244332233 := by
  apply nodeValid_prime [2, 3, 241, 3155147] ⟨164244332233, 5, [(2, 3), (3, 3), (241, 1), (3155147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
    · exact prime_3155147
  · decide +kernel

theorem prime_322157976053 : Nat.Prime 322157976053 := by
  apply nodeValid_prime [2, 11, 23, 28939811] ⟨322157976053, 3, [(2, 2), (11, 2), (23, 1), (28939811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_28939811
  · decide +kernel

theorem prime_323611490159 : Nat.Prime 323611490159 := by
  apply nodeValid_prime [2, 11, 29, 331, 491, 3121] ⟨323611490159, 11, [(2, 1), (11, 1), (29, 1), (331, 1), (491, 1), (3121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_331
    · exact prime_491
    · exact prime_3121
  · decide +kernel

theorem prime_328488655151 : Nat.Prime 328488655151 := by
  apply nodeValid_prime [2, 5, 43, 152785421] ⟨328488655151, 13, [(2, 1), (5, 2), (43, 1), (152785421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_152785421
  · decide +kernel

theorem prime_330945827501 : Nat.Prime 330945827501 := by
  apply nodeValid_prime [2, 5, 163, 812137] ⟨330945827501, 2, [(2, 2), (5, 4), (163, 1), (812137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_812137
  · decide +kernel

theorem prime_643348860589 : Nat.Prime 643348860589 := by
  apply nodeValid_prime [2, 3, 7, 269, 9490601] ⟨643348860589, 6, [(2, 2), (3, 2), (7, 1), (269, 1), (9490601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_269
    · exact prime_9490601
  · decide +kernel

theorem prime_643348860787 : Nat.Prime 643348860787 := by
  apply nodeValid_prime [2, 3, 131, 1471, 185477] ⟨643348860787, 2, [(2, 1), (3, 2), (131, 1), (1471, 1), (185477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_1471
    · exact prime_185477
  · decide +kernel

theorem prime_643348907609 : Nat.Prime 643348907609 := by
  apply nodeValid_prime [2, 11, 31, 191, 1234721] ⟨643348907609, 6, [(2, 3), (11, 1), (31, 1), (191, 1), (1234721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_191
    · exact prime_1234721
  · decide +kernel

theorem prime_644315947799 : Nat.Prime 644315947799 := by
  apply nodeValid_prime [2, 39233, 8211403] ⟨644315947799, 17, [(2, 1), (39233, 1), (8211403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_39233
    · exact prime_8211403
  · decide +kernel

theorem prime_644315951711 : Nat.Prime 644315951711 := by
  apply nodeValid_prime [2, 5, 64431595171] ⟨644315951711, 11, [(2, 1), (5, 1), (64431595171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_64431595171
  · decide +kernel

theorem prime_644315952107 : Nat.Prime 644315952107 := by
  apply nodeValid_prime [2, 322157976053] ⟨644315952107, 2, [(2, 1), (322157976053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_322157976053
  · decide +kernel

theorem prime_645283950461 : Nat.Prime 645283950461 := by
  apply nodeValid_prime [2, 5, 2251, 2269, 6317] ⟨645283950461, 2, [(2, 2), (5, 1), (2251, 1), (2269, 1), (6317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2251
    · exact prime_2269
    · exact prime_6317
  · decide +kernel

theorem prime_645283953383 : Nat.Prime 645283953383 := by
  apply nodeValid_prime [2, 4297, 75085403] ⟨645283953383, 5, [(2, 1), (4297, 1), (75085403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4297
    · exact prime_75085403
  · decide +kernel

theorem prime_645283971853 : Nat.Prime 645283971853 := by
  apply nodeValid_prime [2, 3, 13, 19, 2447, 88969] ⟨645283971853, 5, [(2, 2), (3, 1), (13, 1), (19, 1), (2447, 1), (88969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_2447
    · exact prime_88969
  · decide +kernel

theorem prime_646252982339 : Nat.Prime 646252982339 := by
  apply nodeValid_prime [2, 17, 31, 47, 157, 83093] ⟨646252982339, 2, [(2, 1), (17, 1), (31, 1), (47, 1), (157, 1), (83093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_31
    · exact prime_47
    · exact prime_157
    · exact prime_83093
  · decide +kernel

theorem prime_646253019107 : Nat.Prime 646253019107 := by
  apply nodeValid_prime [2, 419, 771184987] ⟨646253019107, 2, [(2, 1), (419, 1), (771184987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_771184987
  · decide +kernel

theorem prime_646253019869 : Nat.Prime 646253019869 := by
  apply nodeValid_prime [2, 29, 1873, 2974451] ⟨646253019869, 2, [(2, 2), (29, 1), (1873, 1), (2974451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1873
    · exact prime_2974451
  · decide +kernel

theorem prime_647222980319 : Nat.Prime 647222980319 := by
  apply nodeValid_prime [2, 323611490159] ⟨647222980319, 11, [(2, 1), (323611490159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_323611490159
  · decide +kernel

theorem prime_647223043807 : Nat.Prime 647223043807 := by
  apply nodeValid_prime [2, 3, 35956835767] ⟨647223043807, 3, [(2, 1), (3, 2), (35956835767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35956835767
  · decide +kernel

theorem prime_647223046837 : Nat.Prime 647223046837 := by
  apply nodeValid_prime [2, 3, 53935253903] ⟨647223046837, 5, [(2, 2), (3, 1), (53935253903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53935253903
  · decide +kernel

theorem prime_648193964179 : Nat.Prime 648193964179 := by
  apply nodeValid_prime [2, 3, 108032327363] ⟨648193964179, 3, [(2, 1), (3, 1), (108032327363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_108032327363
  · decide +kernel

theorem prime_648194005717 : Nat.Prime 648194005717 := by
  apply nodeValid_prime [2, 3, 5351, 10094593] ⟨648194005717, 6, [(2, 2), (3, 1), (5351, 1), (10094593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5351
    · exact prime_10094593
  · decide +kernel

theorem prime_648194005993 : Nat.Prime 648194005993 := by
  apply nodeValid_prime [2, 3, 13, 17, 29, 4214087] ⟨648194005993, 11, [(2, 3), (3, 1), (13, 1), (17, 1), (29, 1), (4214087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_29
    · exact prime_4214087
  · decide +kernel

theorem prime_649165927831 : Nat.Prime 649165927831 := by
  apply nodeValid_prime [2, 3, 5, 7, 367, 2663, 3163] ⟨649165927831, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (367, 1), (2663, 1), (3163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_367
    · exact prime_2663
    · exact prime_3163
  · decide +kernel

theorem prime_649165928491 : Nat.Prime 649165928491 := by
  apply nodeValid_prime [2, 3, 5, 103, 7457, 9391] ⟨649165928491, 2, [(2, 1), (3, 2), (5, 1), (103, 1), (7457, 1), (9391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_7457
    · exact prime_9391
  · decide +kernel

theorem prime_649165928563 : Nat.Prime 649165928563 := by
  apply nodeValid_prime [2, 3, 193, 186864113] ⟨649165928563, 2, [(2, 1), (3, 2), (193, 1), (186864113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_193
    · exact prime_186864113
  · decide +kernel

theorem prime_650138882123 : Nat.Prime 650138882123 := by
  apply nodeValid_prime [2, 397, 818814713] ⟨650138882123, 2, [(2, 1), (397, 1), (818814713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_818814713
  · decide +kernel

theorem prime_650138906167 : Nat.Prime 650138906167 := by
  apply nodeValid_prime [2, 3, 21881, 4952081] ⟨650138906167, 6, [(2, 1), (3, 1), (21881, 1), (4952081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21881
    · exact prime_4952081
  · decide +kernel

theorem prime_650138906567 : Nat.Prime 650138906567 := by
  apply nodeValid_prime [2, 53, 491, 887, 14083] ⟨650138906567, 5, [(2, 1), (53, 1), (491, 1), (887, 1), (14083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_491
    · exact prime_887
    · exact prime_14083
  · decide +kernel

theorem prime_651112828759 : Nat.Prime 651112828759 := by
  apply nodeValid_prime [2, 3, 7, 8597, 200363] ⟨651112828759, 12, [(2, 1), (3, 3), (7, 1), (8597, 1), (200363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8597
    · exact prime_200363
  · decide +kernel

theorem prime_651112853291 : Nat.Prime 651112853291 := by
  apply nodeValid_prime [2, 5, 65111285329] ⟨651112853291, 2, [(2, 1), (5, 1), (65111285329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_65111285329
  · decide +kernel

theorem prime_651112853767 : Nat.Prime 651112853767 := by
  apply nodeValid_prime [2, 3, 19213, 5648197] ⟨651112853767, 3, [(2, 1), (3, 1), (19213, 1), (5648197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19213
    · exact prime_5648197
  · decide +kernel

theorem prime_652087768831 : Nat.Prime 652087768831 := by
  apply nodeValid_prime [2, 3, 5, 709, 30657629] ⟨652087768831, 13, [(2, 1), (3, 1), (5, 1), (709, 1), (30657629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_709
    · exact prime_30657629
  · decide +kernel

theorem prime_652087788769 : Nat.Prime 652087788769 := by
  apply nodeValid_prime [2, 3, 13, 19352083] ⟨652087788769, 11, [(2, 5), (3, 4), (13, 1), (19352083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19352083
  · decide +kernel

theorem prime_653063650531 : Nat.Prime 653063650531 := by
  apply nodeValid_prime [2, 3, 5, 1399, 15560249] ⟨653063650531, 2, [(2, 1), (3, 1), (5, 1), (1399, 1), (15560249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1399
    · exact prime_15560249
  · decide +kernel

theorem prime_653063651083 : Nat.Prime 653063651083 := by
  apply nodeValid_prime [2, 3, 119627, 303287] ⟨653063651083, 2, [(2, 1), (3, 2), (119627, 1), (303287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_119627
    · exact prime_303287
  · decide +kernel

theorem prime_653063698759 : Nat.Prime 653063698759 := by
  apply nodeValid_prime [2, 3, 47, 2909, 796091] ⟨653063698759, 6, [(2, 1), (3, 1), (47, 1), (2909, 1), (796091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_2909
    · exact prime_796091
  · decide +kernel

theorem prime_654040614641 : Nat.Prime 654040614641 := by
  apply nodeValid_prime [2, 5, 7, 103, 197, 57559] ⟨654040614641, 3, [(2, 4), (5, 1), (7, 1), (103, 1), (197, 1), (57559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_103
    · exact prime_197
    · exact prime_57559
  · decide +kernel

theorem prime_654040624927 : Nat.Prime 654040624927 := by
  apply nodeValid_prime [2, 3, 13, 8385136217] ⟨654040624927, 3, [(2, 1), (3, 1), (13, 1), (8385136217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_8385136217
  · decide +kernel

theorem prime_654040625683 : Nat.Prime 654040625683 := by
  apply nodeValid_prime [2, 3, 1193, 91371979] ⟨654040625683, 2, [(2, 1), (3, 1), (1193, 1), (91371979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1193
    · exact prime_91371979
  · decide +kernel

theorem prime_655018480997 : Nat.Prime 655018480997 := by
  apply nodeValid_prime [2, 11, 2251, 601219] ⟨655018480997, 2, [(2, 2), (11, 2), (2251, 1), (601219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2251
    · exact prime_601219
  · decide +kernel

theorem prime_655018481219 : Nat.Prime 655018481219 := by
  apply nodeValid_prime [2, 131, 42359, 59021] ⟨655018481219, 2, [(2, 1), (131, 1), (42359, 1), (59021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_42359
    · exact prime_59021
  · decide +kernel

theorem prime_655018521517 : Nat.Prime 655018521517 := by
  apply nodeValid_prime [2, 3, 41521, 438211] ⟨655018521517, 2, [(2, 2), (3, 2), (41521, 1), (438211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41521
    · exact prime_438211
  · decide +kernel

theorem prime_655997399041 : Nat.Prime 655997399041 := by
  apply nodeValid_prime [2, 3, 5, 173, 61717] ⟨655997399041, 7, [(2, 12), (3, 1), (5, 1), (173, 1), (61717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_61717
  · decide +kernel

theorem prime_655997399201 : Nat.Prime 655997399201 := by
  apply nodeValid_prime [2, 5, 11, 13, 5734243] ⟨655997399201, 3, [(2, 5), (5, 2), (11, 1), (13, 1), (5734243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_5734243
  · decide +kernel

theorem prime_655997419151 : Nat.Prime 655997419151 := by
  apply nodeValid_prime [2, 5, 13119948383] ⟨655997419151, 19, [(2, 1), (5, 2), (13119948383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13119948383
  · decide +kernel

theorem prime_656977310303 : Nat.Prime 656977310303 := by
  apply nodeValid_prime [2, 328488655151] ⟨656977310303, 5, [(2, 1), (328488655151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_328488655151
  · decide +kernel

theorem prime_656977328933 : Nat.Prime 656977328933 := by
  apply nodeValid_prime [2, 164244332233] ⟨656977328933, 2, [(2, 2), (164244332233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_164244332233
  · decide +kernel

theorem prime_656977329571 : Nat.Prime 656977329571 := by
  apply nodeValid_prime [2, 3, 5, 1187, 18449237] ⟨656977329571, 2, [(2, 1), (3, 1), (5, 1), (1187, 1), (18449237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1187
    · exact prime_18449237
  · decide +kernel

theorem prime_657958184581 : Nat.Prime 657958184581 := by
  apply nodeValid_prime [2, 3, 5, 109, 271, 371237] ⟨657958184581, 2, [(2, 2), (3, 1), (5, 1), (109, 1), (271, 1), (371237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_271
    · exact prime_371237
  · decide +kernel

theorem prime_657958201757 : Nat.Prime 657958201757 := by
  apply nodeValid_prime [2, 67, 263, 383, 24373] ⟨657958201757, 2, [(2, 2), (67, 1), (263, 1), (383, 1), (24373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_263
    · exact prime_383
    · exact prime_24373
  · decide +kernel

theorem prime_657958203677 : Nat.Prime 657958203677 := by
  apply nodeValid_prime [2, 52223, 3149753] ⟨657958203677, 2, [(2, 2), (52223, 1), (3149753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_52223
    · exact prime_3149753
  · decide +kernel

theorem prime_658940052403 : Nat.Prime 658940052403 := by
  apply nodeValid_prime [2, 3, 12202593563] ⟨658940052403, 2, [(2, 1), (3, 3), (12202593563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12202593563
  · decide +kernel

theorem prime_658940075741 : Nat.Prime 658940075741 := by
  apply nodeValid_prime [2, 5, 59, 73, 7649641] ⟨658940075741, 2, [(2, 2), (5, 1), (59, 1), (73, 1), (7649641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_73
    · exact prime_7649641
  · decide +kernel

theorem prime_658940076233 : Nat.Prime 658940076233 := by
  apply nodeValid_prime [2, 139, 1949, 304039] ⟨658940076233, 3, [(2, 3), (139, 1), (1949, 1), (304039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_1949
    · exact prime_304039
  · decide +kernel

theorem prime_659922917821 : Nat.Prime 659922917821 := by
  apply nodeValid_prime [2, 3, 5, 173, 487, 130547] ⟨659922917821, 2, [(2, 2), (3, 1), (5, 1), (173, 1), (487, 1), (130547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_173
    · exact prime_487
    · exact prime_130547
  · decide +kernel

theorem prime_659922918289 : Nat.Prime 659922918289 := by
  apply nodeValid_prime [2, 3, 7229, 1901839] ⟨659922918289, 7, [(2, 4), (3, 1), (7229, 1), (1901839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7229
    · exact prime_1901839
  · decide +kernel

theorem prime_659922920851 : Nat.Prime 659922920851 := by
  apply nodeValid_prime [2, 3, 5, 3637, 1209647] ⟨659922920851, 10, [(2, 1), (3, 1), (5, 2), (3637, 1), (1209647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3637
    · exact prime_1209647
  · decide +kernel

theorem prime_660906777721 : Nat.Prime 660906777721 := by
  apply nodeValid_prime [2, 3, 5, 7, 786793783] ⟨660906777721, 13, [(2, 3), (3, 1), (5, 1), (7, 1), (786793783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_786793783
  · decide +kernel

theorem prime_660906780811 : Nat.Prime 660906780811 := by
  apply nodeValid_prime [2, 3, 5, 157, 140319911] ⟨660906780811, 3, [(2, 1), (3, 1), (5, 1), (157, 1), (140319911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_157
    · exact prime_140319911
  · decide +kernel

theorem prime_661891629173 : Nat.Prime 661891629173 := by
  apply nodeValid_prime [2, 17, 9733700429] ⟨661891629173, 2, [(2, 2), (17, 1), (9733700429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_9733700429
  · decide +kernel

theorem prime_661891652143 : Nat.Prime 661891652143 := by
  apply nodeValid_prime [2, 3, 7, 61, 258349591] ⟨661891652143, 5, [(2, 1), (3, 1), (7, 1), (61, 1), (258349591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_258349591
  · decide +kernel

theorem prime_661891655003 : Nat.Prime 661891655003 := by
  apply nodeValid_prime [2, 330945827501] ⟨661891655003, 2, [(2, 1), (330945827501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_330945827501
  · decide +kernel

theorem prime_662877469103 : Nat.Prime 662877469103 := by
  apply nodeValid_prime [2, 457837, 723923] ⟨662877469103, 5, [(2, 1), (457837, 1), (723923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457837
    · exact prime_723923
  · decide +kernel

theorem prime_662877480011 : Nat.Prime 662877480011 := by
  apply nodeValid_prime [2, 5, 66287748001] ⟨662877480011, 2, [(2, 1), (5, 1), (66287748001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_66287748001
  · decide +kernel

theorem prime_662877481571 : Nat.Prime 662877481571 := by
  apply nodeValid_prime [2, 5, 37, 1791560761] ⟨662877481571, 2, [(2, 1), (5, 1), (37, 1), (1791560761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1791560761
  · decide +kernel

theorem prime_663864306563 : Nat.Prime 663864306563 := by
  apply nodeValid_prime [2, 67, 8677, 570959] ⟨663864306563, 2, [(2, 1), (67, 1), (8677, 1), (570959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_8677
    · exact prime_570959
  · decide +kernel

theorem prime_663864306631 : Nat.Prime 663864306631 := by
  apply nodeValid_prime [2, 3, 5, 7, 4327, 730589] ⟨663864306631, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (4327, 1), (730589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_4327
    · exact prime_730589
  · decide +kernel

theorem prime_663864306733 : Nat.Prime 663864306733 := by
  apply nodeValid_prime [2, 3, 11, 9787, 57097] ⟨663864306733, 6, [(2, 2), (3, 3), (11, 1), (9787, 1), (57097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9787
    · exact prime_57097
  · decide +kernel

theorem prime_664852095899 : Nat.Prime 664852095899 := by
  apply nodeValid_prime [2, 41, 5881, 1378669] ⟨664852095899, 2, [(2, 1), (41, 1), (5881, 1), (1378669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_5881
    · exact prime_1378669
  · decide +kernel

theorem prime_664852098733 : Nat.Prime 664852098733 := by
  apply nodeValid_prime [2, 3, 53611, 1033451] ⟨664852098733, 5, [(2, 2), (3, 1), (53611, 1), (1033451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53611
    · exact prime_1033451
  · decide +kernel

theorem prime_664852133789 : Nat.Prime 664852133789 := by
  apply nodeValid_prime [2, 61, 941, 2895647] ⟨664852133789, 2, [(2, 2), (61, 1), (941, 1), (2895647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_941
    · exact prime_2895647
  · decide +kernel

theorem prime_665840954971 : Nat.Prime 665840954971 := by
  apply nodeValid_prime [2, 3, 5, 29, 85037159] ⟨665840954971, 3, [(2, 1), (3, 3), (5, 1), (29, 1), (85037159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_85037159
  · decide +kernel

theorem prime_665840955007 : Nat.Prime 665840955007 := by
  apply nodeValid_prime [2, 3, 36991164167] ⟨665840955007, 3, [(2, 1), (3, 2), (36991164167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36991164167
  · decide +kernel

theorem prime_665840956357 : Nat.Prime 665840956357 := by
  apply nodeValid_prime [2, 3, 337, 54883033] ⟨665840956357, 5, [(2, 2), (3, 2), (337, 1), (54883033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
    · exact prime_54883033
  · decide +kernel

theorem prime_666830777401 : Nat.Prime 666830777401 := by
  apply nodeValid_prime [2, 3, 5, 123487181] ⟨666830777401, 28, [(2, 3), (3, 3), (5, 2), (123487181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_123487181
  · decide +kernel

theorem prime_666830792539 : Nat.Prime 666830792539 := by
  apply nodeValid_prime [2, 3, 19, 593, 3288023] ⟨666830792539, 2, [(2, 1), (3, 2), (19, 1), (593, 1), (3288023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_593
    · exact prime_3288023
  · decide +kernel

theorem prime_666830796703 : Nat.Prime 666830796703 := by
  apply nodeValid_prime [2, 3, 7, 15876923731] ⟨666830796703, 7, [(2, 1), (3, 1), (7, 1), (15876923731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_15876923731
  · decide +kernel

end Sude.Lucas.Generated
