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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0091
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0113
import Sude.GeneratedFTT.N0123

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11681 : Nat.Prime 11681 := by
  apply nodeValid_prime [2, 5, 73] ⟨11681, 3, [(2, 5), (5, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_15361 : Nat.Prime 15361 := by
  apply nodeValid_prime [2, 3, 5] ⟨15361, 7, [(2, 10), (3, 1), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_16633 : Nat.Prime 16633 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨16633, 15, [(2, 3), (3, 3), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_16651 : Nat.Prime 16651 := by
  apply nodeValid_prime [2, 3, 5, 37] ⟨16651, 2, [(2, 1), (3, 2), (5, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel

theorem prime_17939 : Nat.Prime 17939 := by
  apply nodeValid_prime [2, 8969] ⟨17939, 2, [(2, 1), (8969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8969
  · decide +kernel

theorem prime_19031 : Nat.Prime 19031 := by
  apply nodeValid_prime [2, 5, 11, 173] ⟨19031, 11, [(2, 1), (5, 1), (11, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_173
  · decide +kernel

theorem prime_25981 : Nat.Prime 25981 := by
  apply nodeValid_prime [2, 3, 5, 433] ⟨25981, 11, [(2, 2), (3, 1), (5, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_433
  · decide +kernel

theorem prime_38201 : Nat.Prime 38201 := by
  apply nodeValid_prime [2, 5, 191] ⟨38201, 3, [(2, 3), (5, 2), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_191
  · decide +kernel

theorem prime_38501 : Nat.Prime 38501 := by
  apply nodeValid_prime [2, 5, 7, 11] ⟨38501, 2, [(2, 2), (5, 3), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_40973 : Nat.Prime 40973 := by
  apply nodeValid_prime [2, 10243] ⟨40973, 2, [(2, 2), (10243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10243
  · decide +kernel

theorem prime_42071 : Nat.Prime 42071 := by
  apply nodeValid_prime [2, 5, 7, 601] ⟨42071, 7, [(2, 1), (5, 1), (7, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_601
  · decide +kernel

theorem prime_42073 : Nat.Prime 42073 := by
  apply nodeValid_prime [2, 3, 1753] ⟨42073, 5, [(2, 3), (3, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1753
  · decide +kernel

theorem prime_44483 : Nat.Prime 44483 := by
  apply nodeValid_prime [2, 23, 967] ⟨44483, 2, [(2, 1), (23, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_967
  · decide +kernel

theorem prime_45893 : Nat.Prime 45893 := by
  apply nodeValid_prime [2, 7, 11, 149] ⟨45893, 2, [(2, 2), (7, 1), (11, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_149
  · decide +kernel

theorem prime_46877 : Nat.Prime 46877 := by
  apply nodeValid_prime [2, 11719] ⟨46877, 2, [(2, 2), (11719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11719
  · decide +kernel

theorem prime_47969 : Nat.Prime 47969 := by
  apply nodeValid_prime [2, 1499] ⟨47969, 3, [(2, 5), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1499
  · decide +kernel

theorem prime_53327 : Nat.Prime 53327 := by
  apply nodeValid_prime [2, 7, 13, 293] ⟨53327, 5, [(2, 1), (7, 1), (13, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_293
  · decide +kernel

theorem prime_57347 : Nat.Prime 57347 := by
  apply nodeValid_prime [2, 53, 541] ⟨57347, 2, [(2, 1), (53, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_541
  · decide +kernel

theorem prime_61357 : Nat.Prime 61357 := by
  apply nodeValid_prime [2, 3, 5113] ⟨61357, 6, [(2, 2), (3, 1), (5113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5113
  · decide +kernel

theorem prime_65837 : Nat.Prime 65837 := by
  apply nodeValid_prime [2, 109, 151] ⟨65837, 2, [(2, 2), (109, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_151
  · decide +kernel

theorem prime_70913 : Nat.Prime 70913 := by
  apply nodeValid_prime [2, 277] ⟨70913, 3, [(2, 8), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_277
  · decide +kernel

theorem prime_76403 : Nat.Prime 76403 := by
  apply nodeValid_prime [2, 38201] ⟨76403, 2, [(2, 1), (38201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38201
  · decide +kernel

theorem prime_83449 : Nat.Prime 83449 := by
  apply nodeValid_prime [2, 3, 19, 61] ⟨83449, 13, [(2, 3), (3, 2), (19, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
  · decide +kernel

theorem prime_86923 : Nat.Prime 86923 := by
  apply nodeValid_prime [2, 3, 11, 439] ⟨86923, 2, [(2, 1), (3, 2), (11, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_439
  · decide +kernel

theorem prime_92849 : Nat.Prime 92849 := by
  apply nodeValid_prime [2, 7, 829] ⟨92849, 3, [(2, 4), (7, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_829
  · decide +kernel

theorem prime_118369 : Nat.Prime 118369 := by
  apply nodeValid_prime [2, 3, 137] ⟨118369, 7, [(2, 5), (3, 3), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_119039 : Nat.Prime 119039 := by
  apply nodeValid_prime [2, 53, 1123] ⟨119039, 7, [(2, 1), (53, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1123
  · decide +kernel

theorem prime_120833 : Nat.Prime 120833 := by
  apply nodeValid_prime [2, 59] ⟨120833, 3, [(2, 11), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_59
  · decide +kernel

theorem prime_130957 : Nat.Prime 130957 := by
  apply nodeValid_prime [2, 3, 7, 1559] ⟨130957, 2, [(2, 2), (3, 1), (7, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1559
  · decide +kernel

theorem prime_144671 : Nat.Prime 144671 := by
  apply nodeValid_prime [2, 5, 17, 23, 37] ⟨144671, 7, [(2, 1), (5, 1), (17, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_171329 : Nat.Prime 171329 := by
  apply nodeValid_prime [2, 2677] ⟨171329, 3, [(2, 6), (2677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2677
  · decide +kernel

theorem prime_184333 : Nat.Prime 184333 := by
  apply nodeValid_prime [2, 3, 15361] ⟨184333, 5, [(2, 2), (3, 1), (15361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15361
  · decide +kernel

theorem prime_185699 : Nat.Prime 185699 := by
  apply nodeValid_prime [2, 92849] ⟨185699, 2, [(2, 1), (92849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_92849
  · decide +kernel

theorem prime_187507 : Nat.Prime 187507 := by
  apply nodeValid_prime [2, 3, 11, 947] ⟨187507, 3, [(2, 1), (3, 2), (11, 1), (947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_947
  · decide +kernel

theorem prime_234103 : Nat.Prime 234103 := by
  apply nodeValid_prime [2, 3, 11, 3547] ⟨234103, 3, [(2, 1), (3, 1), (11, 1), (3547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_3547
  · decide +kernel

theorem prime_251393 : Nat.Prime 251393 := by
  apply nodeValid_prime [2, 491] ⟨251393, 3, [(2, 9), (491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_491
  · decide +kernel

theorem prime_266899 : Nat.Prime 266899 := by
  apply nodeValid_prime [2, 3, 44483] ⟨266899, 3, [(2, 1), (3, 1), (44483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_44483
  · decide +kernel

theorem prime_282683 : Nat.Prime 282683 := by
  apply nodeValid_prime [2, 19, 43, 173] ⟨282683, 2, [(2, 1), (19, 1), (43, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_43
    · exact prime_173
  · decide +kernel

theorem prime_289343 : Nat.Prime 289343 := by
  apply nodeValid_prime [2, 144671] ⟨289343, 5, [(2, 1), (144671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_144671
  · decide +kernel

theorem prime_344083 : Nat.Prime 344083 := by
  apply nodeValid_prime [2, 3, 57347] ⟨344083, 2, [(2, 1), (3, 1), (57347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_57347
  · decide +kernel

theorem prime_355853 : Nat.Prime 355853 := by
  apply nodeValid_prime [2, 7, 71, 179] ⟨355853, 2, [(2, 2), (7, 1), (71, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_179
  · decide +kernel

theorem prime_385739 : Nat.Prime 385739 := by
  apply nodeValid_prime [2, 19, 10151] ⟨385739, 2, [(2, 1), (19, 1), (10151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_10151
  · decide +kernel

theorem prime_407191 : Nat.Prime 407191 := by
  apply nodeValid_prime [2, 3, 5, 7, 277] ⟨407191, 3, [(2, 1), (3, 1), (5, 1), (7, 2), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_277
  · decide +kernel

theorem prime_467833 : Nat.Prime 467833 := by
  apply nodeValid_prime [2, 3, 101, 193] ⟨467833, 5, [(2, 3), (3, 1), (101, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_193
  · decide +kernel

theorem prime_539237 : Nat.Prime 539237 := by
  apply nodeValid_prime [2, 113, 1193] ⟨539237, 2, [(2, 2), (113, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_1193
  · decide +kernel

theorem prime_586609 : Nat.Prime 586609 := by
  apply nodeValid_prime [2, 3, 11, 101] ⟨586609, 17, [(2, 4), (3, 1), (11, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_101
  · decide +kernel

theorem prime_598789 : Nat.Prime 598789 := by
  apply nodeValid_prime [2, 3, 16633] ⟨598789, 6, [(2, 2), (3, 2), (16633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16633
  · decide +kernel

theorem prime_638263 : Nat.Prime 638263 := by
  apply nodeValid_prime [2, 3, 59, 601] ⟨638263, 5, [(2, 1), (3, 2), (59, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_601
  · decide +kernel

theorem prime_853843 : Nat.Prime 853843 := by
  apply nodeValid_prime [2, 3, 11, 17, 761] ⟨853843, 31, [(2, 1), (3, 1), (11, 1), (17, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_761
  · decide +kernel

theorem prime_921013 : Nat.Prime 921013 := by
  apply nodeValid_prime [2, 3, 23, 47, 71] ⟨921013, 2, [(2, 2), (3, 1), (23, 1), (47, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_47
    · exact prime_71
  · decide +kernel

theorem prime_934561 : Nat.Prime 934561 := by
  apply nodeValid_prime [2, 3, 5, 11, 59] ⟨934561, 7, [(2, 5), (3, 2), (5, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_1034513 : Nat.Prime 1034513 := by
  apply nodeValid_prime [2, 19, 41, 83] ⟨1034513, 3, [(2, 4), (19, 1), (41, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41
    · exact prime_83
  · decide +kernel

theorem prime_1155001 : Nat.Prime 1155001 := by
  apply nodeValid_prime [2, 3, 5, 7, 11] ⟨1155001, 23, [(2, 3), (3, 1), (5, 4), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_1455847 : Nat.Prime 1455847 := by
  apply nodeValid_prime [2, 3, 7, 17, 2039] ⟨1455847, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_2039
  · decide +kernel

theorem prime_1588877 : Nat.Prime 1588877 := by
  apply nodeValid_prime [2, 491, 809] ⟨1588877, 2, [(2, 2), (491, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_809
  · decide +kernel

theorem prime_1916689 : Nat.Prime 1916689 := by
  apply nodeValid_prime [2, 3, 73, 547] ⟨1916689, 7, [(2, 4), (3, 1), (73, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_547
  · decide +kernel

theorem prime_2034811 : Nat.Prime 2034811 := by
  apply nodeValid_prime [2, 3, 5, 23, 983] ⟨2034811, 7, [(2, 1), (3, 2), (5, 1), (23, 1), (983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_983
  · decide +kernel

theorem prime_2067427 : Nat.Prime 2067427 := by
  apply nodeValid_prime [2, 3, 331, 347] ⟨2067427, 5, [(2, 1), (3, 2), (331, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_331
    · exact prime_347
  · decide +kernel

theorem prime_2090281 : Nat.Prime 2090281 := by
  apply nodeValid_prime [2, 3, 5, 17419] ⟨2090281, 11, [(2, 3), (3, 1), (5, 1), (17419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17419
  · decide +kernel

theorem prime_2197933 : Nat.Prime 2197933 := by
  apply nodeValid_prime [2, 3, 11, 16651] ⟨2197933, 5, [(2, 2), (3, 1), (11, 1), (16651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_16651
  · decide +kernel

theorem prime_2398637 : Nat.Prime 2398637 := by
  apply nodeValid_prime [2, 19, 37, 853] ⟨2398637, 2, [(2, 2), (19, 1), (37, 1), (853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_853
  · decide +kernel

theorem prime_2621023 : Nat.Prime 2621023 := by
  apply nodeValid_prime [2, 3, 43, 10159] ⟨2621023, 17, [(2, 1), (3, 1), (43, 1), (10159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_10159
  · decide +kernel

theorem prime_3108731 : Nat.Prime 3108731 := by
  apply nodeValid_prime [2, 5, 293, 1061] ⟨3108731, 6, [(2, 1), (5, 1), (293, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_293
    · exact prime_1061
  · decide +kernel

theorem prime_3363883 : Nat.Prime 3363883 := by
  apply nodeValid_prime [2, 3, 157, 3571] ⟨3363883, 2, [(2, 1), (3, 1), (157, 1), (3571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_3571
  · decide +kernel

theorem prime_3915341 : Nat.Prime 3915341 := by
  apply nodeValid_prime [2, 5, 11, 13, 37] ⟨3915341, 2, [(2, 2), (5, 1), (11, 1), (13, 1), (37, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_6105947 : Nat.Prime 6105947 := by
  apply nodeValid_prime [2, 7, 11, 31, 1279] ⟨6105947, 2, [(2, 1), (7, 1), (11, 1), (31, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_1279
  · decide +kernel

theorem prime_7031551 : Nat.Prime 7031551 := by
  apply nodeValid_prime [2, 3, 5, 46877] ⟨7031551, 3, [(2, 1), (3, 1), (5, 2), (46877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46877
  · decide +kernel

theorem prime_7637093 : Nat.Prime 7637093 := by
  apply nodeValid_prime [2, 29, 65837] ⟨7637093, 2, [(2, 2), (29, 1), (65837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_65837
  · decide +kernel

theorem prime_8025161 : Nat.Prime 8025161 := by
  apply nodeValid_prime [2, 5, 11, 13, 23, 61] ⟨8025161, 3, [(2, 3), (5, 1), (11, 1), (13, 1), (23, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_61
  · decide +kernel

theorem prime_8519081 : Nat.Prime 8519081 := by
  apply nodeValid_prime [2, 5, 89, 2393] ⟨8519081, 3, [(2, 3), (5, 1), (89, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_2393
  · decide +kernel

theorem prime_10675961 : Nat.Prime 10675961 := by
  apply nodeValid_prime [2, 5, 266899] ⟨10675961, 3, [(2, 3), (5, 1), (266899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_266899
  · decide +kernel

theorem prime_14432543 : Nat.Prime 14432543 := by
  apply nodeValid_prime [2, 881, 8191] ⟨14432543, 5, [(2, 1), (881, 1), (8191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_881
    · exact prime_8191
  · decide +kernel

theorem prime_20690261 : Nat.Prime 20690261 := by
  apply nodeValid_prime [2, 5, 1034513] ⟨20690261, 2, [(2, 2), (5, 1), (1034513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1034513
  · decide +kernel

theorem prime_20902811 : Nat.Prime 20902811 := by
  apply nodeValid_prime [2, 5, 2090281] ⟨20902811, 2, [(2, 1), (5, 1), (2090281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2090281
  · decide +kernel

theorem prime_22773827 : Nat.Prime 22773827 := by
  apply nodeValid_prime [2, 131, 86923] ⟨22773827, 2, [(2, 1), (131, 1), (86923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_86923
  · decide +kernel

theorem prime_23892793 : Nat.Prime 23892793 := by
  apply nodeValid_prime [2, 3, 7, 11, 1847] ⟨23892793, 5, [(2, 3), (3, 1), (7, 2), (11, 1), (1847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1847
  · decide +kernel

theorem prime_41380523 : Nat.Prime 41380523 := by
  apply nodeValid_prime [2, 20690261] ⟨41380523, 2, [(2, 1), (20690261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20690261
  · decide +kernel

theorem prime_41936369 : Nat.Prime 41936369 := by
  apply nodeValid_prime [2, 2621023] ⟨41936369, 3, [(2, 4), (2621023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2621023
  · decide +kernel

theorem prime_42646939 : Nat.Prime 42646939 := by
  apply nodeValid_prime [2, 3, 677, 10499] ⟨42646939, 2, [(2, 1), (3, 1), (677, 1), (10499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_677
    · exact prime_10499
  · decide +kernel

theorem prime_47718967 : Nat.Prime 47718967 := by
  apply nodeValid_prime [2, 3, 17, 467833] ⟨47718967, 6, [(2, 1), (3, 1), (17, 1), (467833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_467833
  · decide +kernel

theorem prime_48589691 : Nat.Prime 48589691 := by
  apply nodeValid_prime [2, 5, 983, 4943] ⟨48589691, 2, [(2, 1), (5, 1), (983, 1), (4943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_983
    · exact prime_4943
  · decide +kernel

theorem prime_68152649 : Nat.Prime 68152649 := by
  apply nodeValid_prime [2, 8519081] ⟨68152649, 3, [(2, 3), (8519081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8519081
  · decide +kernel

theorem prime_68409287 : Nat.Prime 68409287 := by
  apply nodeValid_prime [2, 11, 282683] ⟨68409287, 5, [(2, 1), (11, 2), (282683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_282683
  · decide +kernel

theorem prime_71772247 : Nat.Prime 71772247 := by
  apply nodeValid_prime [2, 3, 7, 13, 43, 1019] ⟨71772247, 5, [(2, 1), (3, 2), (7, 1), (13, 1), (43, 1), (1019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_1019
  · decide +kernel

theorem prime_71905783 : Nat.Prime 71905783 := by
  apply nodeValid_prime [2, 3, 13, 70913] ⟨71905783, 3, [(2, 1), (3, 1), (13, 2), (70913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_70913
  · decide +kernel

theorem prime_75076951 : Nat.Prime 75076951 := by
  apply nodeValid_prime [2, 3, 5, 13, 38501] ⟨75076951, 6, [(2, 1), (3, 1), (5, 2), (13, 1), (38501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_38501
  · decide +kernel

theorem prime_87801383 : Nat.Prime 87801383 := by
  apply nodeValid_prime [2, 137, 2339] ⟨87801383, 5, [(2, 1), (137, 2), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_2339
  · decide +kernel

theorem prime_114019363 : Nat.Prime 114019363 := by
  apply nodeValid_prime [2, 3, 487, 13007] ⟨114019363, 2, [(2, 1), (3, 2), (487, 1), (13007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_487
    · exact prime_13007
  · decide +kernel

theorem prime_127976977 : Nat.Prime 127976977 := by
  apply nodeValid_prime [2, 3, 296243] ⟨127976977, 5, [(2, 4), (3, 3), (296243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_296243
  · decide +kernel

theorem prime_136642963 : Nat.Prime 136642963 := by
  apply nodeValid_prime [2, 3, 22773827] ⟨136642963, 2, [(2, 1), (3, 1), (22773827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22773827
  · decide +kernel

theorem prime_141933199 : Nat.Prime 141933199 := by
  apply nodeValid_prime [2, 3, 11, 113, 19031] ⟨141933199, 6, [(2, 1), (3, 1), (11, 1), (113, 1), (19031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
    · exact prime_19031
  · decide +kernel

theorem prime_193580971 : Nat.Prime 193580971 := by
  apply nodeValid_prime [2, 3, 5, 11, 586609] ⟨193580971, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (586609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_586609
  · decide +kernel

theorem prime_298493113 : Nat.Prime 298493113 := by
  apply nodeValid_prime [2, 3, 12437213] ⟨298493113, 5, [(2, 3), (3, 1), (12437213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12437213
  · decide +kernel

theorem prime_506669773 : Nat.Prime 506669773 := by
  apply nodeValid_prime [2, 3, 7, 103, 157, 373] ⟨506669773, 6, [(2, 2), (3, 1), (7, 1), (103, 1), (157, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_157
    · exact prime_373
  · decide +kernel

theorem prime_767861863 : Nat.Prime 767861863 := by
  apply nodeValid_prime [2, 3, 127976977] ⟨767861863, 3, [(2, 1), (3, 1), (127976977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127976977
  · decide +kernel

theorem prime_1007208833 : Nat.Prime 1007208833 := by
  apply nodeValid_prime [2, 7, 109, 10313] ⟨1007208833, 5, [(2, 7), (7, 1), (109, 1), (10313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109
    · exact prime_10313
  · decide +kernel

theorem prime_1449995927 : Nat.Prime 1449995927 := by
  apply nodeValid_prime [2, 17, 42646939] ⟨1449995927, 5, [(2, 1), (17, 1), (42646939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_42646939
  · decide +kernel

theorem prime_1823788531 : Nat.Prime 1823788531 := by
  apply nodeValid_prime [2, 3, 5, 19, 59, 18077] ⟨1823788531, 2, [(2, 1), (3, 2), (5, 1), (19, 1), (59, 1), (18077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_59
    · exact prime_18077
  · decide +kernel

theorem prime_1977365161 : Nat.Prime 1977365161 := by
  apply nodeValid_prime [2, 3, 5, 103, 53327] ⟨1977365161, 11, [(2, 3), (3, 2), (5, 1), (103, 1), (53327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_53327
  · decide +kernel

theorem prime_2153167411 : Nat.Prime 2153167411 := by
  apply nodeValid_prime [2, 3, 5, 71772247] ⟨2153167411, 3, [(2, 1), (3, 1), (5, 1), (71772247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71772247
  · decide +kernel

theorem prime_3108227893 : Nat.Prime 3108227893 := by
  apply nodeValid_prime [2, 3, 7, 11, 3363883] ⟨3108227893, 14, [(2, 2), (3, 1), (7, 1), (11, 1), (3363883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_3363883
  · decide +kernel

theorem prime_3494490361 : Nat.Prime 3494490361 := by
  apply nodeValid_prime [2, 3, 5, 241, 120833] ⟨3494490361, 7, [(2, 3), (3, 1), (5, 1), (241, 1), (120833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
    · exact prime_120833
  · decide +kernel

theorem prime_4560774521 : Nat.Prime 4560774521 := by
  apply nodeValid_prime [2, 5, 114019363] ⟨4560774521, 3, [(2, 3), (5, 1), (114019363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_114019363
  · decide +kernel

theorem prime_5182802557 : Nat.Prime 5182802557 := by
  apply nodeValid_prime [2, 3, 43, 269, 37339] ⟨5182802557, 5, [(2, 2), (3, 1), (43, 1), (269, 1), (37339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_269
    · exact prime_37339
  · decide +kernel

theorem prime_5348916319 : Nat.Prime 5348916319 := by
  apply nodeValid_prime [2, 3, 25981, 34313] ⟨5348916319, 3, [(2, 1), (3, 1), (25981, 1), (34313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25981
    · exact prime_34313
  · decide +kernel

theorem prime_7789834861 : Nat.Prime 7789834861 := by
  apply nodeValid_prime [2, 3, 5, 17, 7637093] ⟨7789834861, 2, [(2, 2), (3, 1), (5, 1), (17, 1), (7637093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_7637093
  · decide +kernel

theorem prime_12919004467 : Nat.Prime 12919004467 := by
  apply nodeValid_prime [2, 3, 2153167411] ⟨12919004467, 2, [(2, 1), (3, 1), (2153167411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2153167411
  · decide +kernel

theorem prime_12945205967 : Nat.Prime 12945205967 := by
  apply nodeValid_prime [2, 7, 11, 23, 1187, 3079] ⟨12945205967, 5, [(2, 1), (7, 1), (11, 1), (23, 1), (1187, 1), (3079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_1187
    · exact prime_3079
  · decide +kernel

theorem prime_21126236333 : Nat.Prime 21126236333 := by
  apply nodeValid_prime [2, 29, 1063, 171329] ⟨21126236333, 2, [(2, 2), (29, 1), (1063, 1), (171329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1063
    · exact prime_171329
  · decide +kernel

theorem prime_27211619951 : Nat.Prime 27211619951 := by
  apply nodeValid_prime [2, 5, 139, 3915341] ⟨27211619951, 37, [(2, 1), (5, 2), (139, 1), (3915341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_3915341
  · decide +kernel

theorem prime_47620918867 : Nat.Prime 47620918867 := by
  apply nodeValid_prime [2, 3, 41, 193580971] ⟨47620918867, 2, [(2, 1), (3, 1), (41, 1), (193580971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_193580971
  · decide +kernel

theorem prime_55911845701 : Nat.Prime 55911845701 := by
  apply nodeValid_prime [2, 3, 5, 17, 135347] ⟨55911845701, 7, [(2, 2), (3, 5), (5, 2), (17, 1), (135347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_135347
  · decide +kernel

theorem prime_59053093109 : Nat.Prime 59053093109 := by
  apply nodeValid_prime [2, 19, 16931, 45893] ⟨59053093109, 2, [(2, 2), (19, 1), (16931, 1), (45893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_16931
    · exact prime_45893
  · decide +kernel

theorem prime_69337391041 : Nat.Prime 69337391041 := by
  apply nodeValid_prime [2, 3, 5, 8025161] ⟨69337391041, 11, [(2, 6), (3, 3), (5, 1), (8025161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8025161
  · decide +kernel

theorem prime_69547267511 : Nat.Prime 69547267511 := by
  apply nodeValid_prime [2, 5, 7, 141933199] ⟨69547267511, 7, [(2, 1), (5, 1), (7, 2), (141933199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_141933199
  · decide +kernel

theorem prime_112928982211 : Nat.Prime 112928982211 := by
  apply nodeValid_prime [2, 3, 5, 11, 1493, 76403] ⟨112928982211, 34, [(2, 1), (3, 2), (5, 1), (11, 1), (1493, 1), (76403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_1493
    · exact prime_76403
  · decide +kernel

theorem prime_149550659543 : Nat.Prime 149550659543 := by
  apply nodeValid_prime [2, 41, 1823788531] ⟨149550659543, 5, [(2, 1), (41, 1), (1823788531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1823788531
  · decide +kernel

theorem prime_151369584293 : Nat.Prime 151369584293 := by
  apply nodeValid_prime [2, 431, 87801383] ⟨151369584293, 2, [(2, 2), (431, 1), (87801383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_87801383
  · decide +kernel

theorem prime_226199364613 : Nat.Prime 226199364613 := by
  apply nodeValid_prime [2, 3, 13, 1449995927] ⟨226199364613, 2, [(2, 2), (3, 1), (13, 1), (1449995927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1449995927
  · decide +kernel

theorem prime_676039562657 : Nat.Prime 676039562657 := by
  apply nodeValid_prime [2, 21126236333] ⟨676039562657, 3, [(2, 5), (21126236333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21126236333
  · decide +kernel

theorem prime_1350035984863 : Nat.Prime 1350035984863 := by
  apply nodeValid_prime [2, 3, 641, 1907, 61357] ⟨1350035984863, 3, [(2, 1), (3, 2), (641, 1), (1907, 1), (61357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_641
    · exact prime_1907
    · exact prime_61357
  · decide +kernel

theorem prime_2689874528483 : Nat.Prime 2689874528483 := by
  apply nodeValid_prime [2, 53, 419, 2129, 28447] ⟨2689874528483, 2, [(2, 1), (53, 1), (419, 1), (2129, 1), (28447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_419
    · exact prime_2129
    · exact prime_28447
  · decide +kernel

theorem prime_2724652544381 : Nat.Prime 2724652544381 := by
  apply nodeValid_prime [2, 5, 13, 43, 10091, 24151] ⟨2724652544381, 2, [(2, 2), (5, 1), (13, 1), (43, 1), (10091, 1), (24151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_10091
    · exact prime_24151
  · decide +kernel

theorem prime_5359406384369 : Nat.Prime 5359406384369 := by
  apply nodeValid_prime [2, 43, 7789834861] ⟨5359406384369, 3, [(2, 4), (43, 1), (7789834861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_7789834861
  · decide +kernel

theorem prime_5359406406359 : Nat.Prime 5359406406359 := by
  apply nodeValid_prime [2, 17, 151, 1117, 934561] ⟨5359406406359, 11, [(2, 1), (17, 1), (151, 1), (1117, 1), (934561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_151
    · exact prime_1117
    · exact prime_934561
  · decide +kernel

theorem prime_5359406406661 : Nat.Prime 5359406406661 := by
  apply nodeValid_prime [2, 3, 5, 151, 4877, 13477] ⟨5359406406661, 6, [(2, 2), (3, 3), (5, 1), (151, 1), (4877, 1), (13477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151
    · exact prime_4877
    · exact prime_13477
  · decide +kernel

theorem prime_5363470744201 : Nat.Prime 5363470744201 := by
  apply nodeValid_prime [2, 3, 5, 59, 1933, 2903] ⟨5363470744201, 7, [(2, 3), (3, 4), (5, 2), (59, 1), (1933, 1), (2903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_1933
    · exact prime_2903
  · decide +kernel

theorem prime_5363470836323 : Nat.Prime 5363470836323 := by
  apply nodeValid_prime [2, 29, 42073, 2197933] ⟨5363470836323, 2, [(2, 1), (29, 1), (42073, 1), (2197933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_42073
    · exact prime_2197933
  · decide +kernel

theorem prime_5363470836697 : Nat.Prime 5363470836697 := by
  apply nodeValid_prime [2, 3, 7, 4560774521] ⟨5363470836697, 10, [(2, 3), (3, 1), (7, 2), (4560774521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_4560774521
  · decide +kernel

theorem prime_5367537187297 : Nat.Prime 5367537187297 := by
  apply nodeValid_prime [2, 3, 55911845701] ⟨5367537187297, 5, [(2, 5), (3, 1), (55911845701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_55911845701
  · decide +kernel

theorem prime_5367537193741 : Nat.Prime 5367537193741 := by
  apply nodeValid_prime [2, 3, 5, 251393, 355853] ⟨5367537193741, 2, [(2, 2), (3, 1), (5, 1), (251393, 1), (355853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_251393
    · exact prime_355853
  · decide +kernel

theorem prime_5367537194497 : Nat.Prime 5367537194497 := by
  apply nodeValid_prime [2, 3, 3494490361] ⟨5367537194497, 10, [(2, 9), (3, 1), (3494490361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3494490361
  · decide +kernel

theorem prime_5371605690149 : Nat.Prime 5371605690149 := by
  apply nodeValid_prime [2, 31, 577, 75076951] ⟨5371605690149, 2, [(2, 2), (31, 1), (577, 1), (75076951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_577
    · exact prime_75076951
  · decide +kernel

theorem prime_5371605690631 : Nat.Prime 5371605690631 := by
  apply nodeValid_prime [2, 3, 5, 4327, 41380523] ⟨5371605690631, 3, [(2, 1), (3, 1), (5, 1), (4327, 1), (41380523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4327
    · exact prime_41380523
  · decide +kernel

theorem prime_5371605715249 : Nat.Prime 5371605715249 := by
  apply nodeValid_prime [2, 3, 23, 587, 1741] ⟨5371605715249, 13, [(2, 4), (3, 3), (23, 3), (587, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_587
    · exact prime_1741
  · decide +kernel

theorem prime_5375676304069 : Nat.Prime 5375676304069 := by
  apply nodeValid_prime [2, 3, 7, 251, 1373, 185699] ⟨5375676304069, 10, [(2, 2), (3, 1), (7, 1), (251, 1), (1373, 1), (185699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_251
    · exact prime_1373
    · exact prime_185699
  · decide +kernel

theorem prime_5375676304253 : Nat.Prime 5375676304253 := by
  apply nodeValid_prime [2, 127, 5521, 1916689] ⟨5375676304253, 2, [(2, 2), (127, 1), (5521, 1), (1916689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_5521
    · exact prime_1916689
  · decide +kernel

theorem prime_5375676337081 : Nat.Prime 5375676337081 := by
  apply nodeValid_prime [2, 3, 5, 7, 89, 71905783] ⟨5375676337081, 11, [(2, 3), (3, 1), (5, 1), (7, 1), (89, 1), (71905783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_89
    · exact prime_71905783
  · decide +kernel

theorem prime_5379749054167 : Nat.Prime 5379749054167 := by
  apply nodeValid_prime [2, 3, 173, 5182802557] ⟨5379749054167, 5, [(2, 1), (3, 1), (173, 1), (5182802557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_5182802557
  · decide +kernel

theorem prime_5379749056967 : Nat.Prime 5379749056967 := by
  apply nodeValid_prime [2, 2689874528483] ⟨5379749056967, 5, [(2, 1), (2689874528483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2689874528483
  · decide +kernel

theorem prime_5379749057467 : Nat.Prime 5379749057467 := by
  apply nodeValid_prime [2, 3, 7, 1787, 23892793] ⟨5379749057467, 3, [(2, 1), (3, 2), (7, 1), (1787, 1), (23892793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1787
    · exact prime_23892793
  · decide +kernel

theorem prime_5383823743549 : Nat.Prime 5383823743549 := by
  apply nodeValid_prime [2, 3, 149550659543] ⟨5383823743549, 2, [(2, 2), (3, 2), (149550659543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149550659543
  · decide +kernel

theorem prime_5383823745331 : Nat.Prime 5383823745331 := by
  apply nodeValid_prime [2, 3, 5, 47, 73, 739, 23593] ⟨5383823745331, 2, [(2, 1), (3, 2), (5, 1), (47, 1), (73, 1), (739, 1), (23593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_73
    · exact prime_739
    · exact prime_23593
  · decide +kernel

theorem prime_5383823864387 : Nat.Prime 5383823864387 := by
  apply nodeValid_prime [2, 11, 118369, 2067427] ⟨5383823864387, 2, [(2, 1), (11, 1), (118369, 1), (2067427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_118369
    · exact prime_2067427
  · decide +kernel

theorem prime_5387900750299 : Nat.Prime 5387900750299 := by
  apply nodeValid_prime [2, 3, 11, 27211619951] ⟨5387900750299, 3, [(2, 1), (3, 2), (11, 1), (27211619951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_27211619951
  · decide +kernel

theorem prime_5387900814161 : Nat.Prime 5387900814161 := by
  apply nodeValid_prime [2, 5, 71, 11831, 80177] ⟨5387900814161, 3, [(2, 4), (5, 1), (71, 1), (11831, 1), (80177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_11831
    · exact prime_80177
  · decide +kernel

theorem prime_5387900816383 : Nat.Prime 5387900816383 := by
  apply nodeValid_prime [2, 3, 7, 19, 23, 41936369] ⟨5387900816383, 6, [(2, 1), (3, 1), (7, 2), (19, 1), (23, 1), (41936369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_23
    · exact prime_41936369
  · decide +kernel

theorem prime_5391979592413 : Nat.Prime 5391979592413 := by
  apply nodeValid_prime [2, 3, 7, 119039, 539237] ⟨5391979592413, 2, [(2, 2), (3, 1), (7, 1), (119039, 1), (539237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_119039
    · exact prime_539237
  · decide +kernel

theorem prime_5391979593233 : Nat.Prime 5391979593233 := by
  apply nodeValid_prime [2, 1129, 298493113] ⟨5391979593233, 3, [(2, 4), (1129, 1), (298493113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1129
    · exact prime_298493113
  · decide +kernel

theorem prime_5391979724267 : Nat.Prime 5391979724267 := by
  apply nodeValid_prime [2, 17, 313, 506669773] ⟨5391979724267, 2, [(2, 1), (17, 1), (313, 1), (506669773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_313
    · exact prime_506669773
  · decide +kernel

theorem prime_5396060659651 : Nat.Prime 5396060659651 := by
  apply nodeValid_prime [2, 3, 5, 1721, 20902811] ⟨5396060659651, 3, [(2, 1), (3, 1), (5, 2), (1721, 1), (20902811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1721
    · exact prime_20902811
  · decide +kernel

theorem prime_5396060660257 : Nat.Prime 5396060660257 := by
  apply nodeValid_prime [2, 3, 7, 41, 3108731] ⟨5396060660257, 5, [(2, 5), (3, 3), (7, 2), (41, 1), (3108731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_3108731
  · decide +kernel

theorem prime_5396060788361 : Nat.Prime 5396060788361 := by
  apply nodeValid_prime [2, 5, 11, 257, 47718967] ⟨5396060788361, 3, [(2, 3), (5, 1), (11, 1), (257, 1), (47718967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_257
    · exact prime_47718967
  · decide +kernel

theorem prime_5400143866739 : Nat.Prime 5400143866739 := by
  apply nodeValid_prime [2, 41, 109, 1009, 598789] ⟨5400143866739, 2, [(2, 1), (41, 1), (109, 1), (1009, 1), (598789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_109
    · exact prime_1009
    · exact prime_598789
  · decide +kernel

theorem prime_5400143867207 : Nat.Prime 5400143867207 := by
  apply nodeValid_prime [2, 11, 19, 12919004467] ⟨5400143867207, 5, [(2, 1), (11, 1), (19, 1), (12919004467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_12919004467
  · decide +kernel

theorem prime_5400143939453 : Nat.Prime 5400143939453 := by
  apply nodeValid_prime [2, 1350035984863] ⟨5400143939453, 2, [(2, 2), (1350035984863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1350035984863
  · decide +kernel

theorem prime_5404229179417 : Nat.Prime 5404229179417 := by
  apply nodeValid_prime [2, 3, 184333, 407191] ⟨5404229179417, 7, [(2, 3), (3, 2), (184333, 1), (407191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_184333
    · exact prime_407191
  · decide +kernel

theorem prime_5404229179673 : Nat.Prime 5404229179673 := by
  apply nodeValid_prime [2, 281, 2239, 3821] ⟨5404229179673, 3, [(2, 3), (281, 2), (2239, 1), (3821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_281
    · exact prime_2239
    · exact prime_3821
  · decide +kernel

theorem prime_5404229186651 : Nat.Prime 5404229186651 := by
  apply nodeValid_prime [2, 5, 7, 113, 136642963] ⟨5404229186651, 2, [(2, 1), (5, 2), (7, 1), (113, 1), (136642963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_113
    · exact prime_136642963
  · decide +kernel

theorem prime_5408316501199 : Nat.Prime 5408316501199 := by
  apply nodeValid_prime [2, 3, 13, 69337391041] ⟨5408316501199, 6, [(2, 1), (3, 1), (13, 1), (69337391041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_69337391041
  · decide +kernel

theorem prime_5408316501257 : Nat.Prime 5408316501257 := by
  apply nodeValid_prime [2, 676039562657] ⟨5408316501257, 3, [(2, 3), (676039562657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_676039562657
  · decide +kernel

theorem prime_5408316533821 : Nat.Prime 5408316533821 := by
  apply nodeValid_prime [2, 3, 5, 29, 3108227893] ⟨5408316533821, 6, [(2, 2), (3, 1), (5, 1), (29, 1), (3108227893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_3108227893
  · decide +kernel

theorem prime_5412405680491 : Nat.Prime 5412405680491 := by
  apply nodeValid_prime [2, 3, 5, 47, 79, 48589691] ⟨5412405680491, 2, [(2, 1), (3, 1), (5, 1), (47, 1), (79, 1), (48589691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_79
    · exact prime_48589691
  · decide +kernel

theorem prime_5412405680603 : Nat.Prime 5412405680603 := by
  apply nodeValid_prime [2, 187507, 14432543] ⟨5412405680603, 2, [(2, 1), (187507, 1), (14432543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_187507
    · exact prime_14432543
  · decide +kernel

theorem prime_5412405968867 : Nat.Prime 5412405968867 := by
  apply nodeValid_prime [2, 13, 17, 179, 68409287] ⟨5412405968867, 2, [(2, 1), (13, 1), (17, 1), (179, 1), (68409287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_179
    · exact prime_68409287
  · decide +kernel

theorem prime_5416497511223 : Nat.Prime 5416497511223 := by
  apply nodeValid_prime [2, 7, 89, 113, 461, 83449] ⟨5416497511223, 5, [(2, 1), (7, 1), (89, 1), (113, 1), (461, 1), (83449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_113
    · exact prime_461
    · exact prime_83449
  · decide +kernel

theorem prime_5416497581603 : Nat.Prime 5416497581603 := by
  apply nodeValid_prime [2, 3527, 767861863] ⟨5416497581603, 2, [(2, 1), (3527, 1), (767861863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3527
    · exact prime_767861863
  · decide +kernel

theorem prime_5416497581771 : Nat.Prime 5416497581771 := by
  apply nodeValid_prime [2, 5, 11, 17, 1823, 1588877] ⟨5416497581771, 2, [(2, 1), (5, 1), (11, 1), (17, 1), (1823, 1), (1588877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
    · exact prime_1823
    · exact prime_1588877
  · decide +kernel

theorem prime_5420591084933 : Nat.Prime 5420591084933 := by
  apply nodeValid_prime [2, 19, 11681, 6105947] ⟨5420591084933, 2, [(2, 2), (19, 1), (11681, 1), (6105947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_11681
    · exact prime_6105947
  · decide +kernel

theorem prime_5420591086219 : Nat.Prime 5420591086219 := by
  apply nodeValid_prime [2, 3, 7, 11, 157, 10675961] ⟨5420591086219, 7, [(2, 1), (3, 1), (7, 2), (11, 1), (157, 1), (10675961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_157
    · exact prime_10675961
  · decide +kernel

theorem prime_5420591146129 : Nat.Prime 5420591146129 := by
  apply nodeValid_prime [2, 3, 112928982211] ⟨5420591146129, 14, [(2, 4), (3, 1), (112928982211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_112928982211
  · decide +kernel

theorem prime_5424686865859 : Nat.Prime 5424686865859 := by
  apply nodeValid_prime [2, 3, 13, 69547267511] ⟨5424686865859, 2, [(2, 1), (3, 1), (13, 1), (69547267511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_69547267511
  · decide +kernel

theorem prime_5424686902379 : Nat.Prime 5424686902379 := by
  apply nodeValid_prime [2, 385739, 7031551] ⟨5424686902379, 2, [(2, 1), (385739, 1), (7031551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_385739
    · exact prime_7031551
  · decide +kernel

theorem prime_5424686902799 : Nat.Prime 5424686902799 := by
  apply nodeValid_prime [2, 29, 1163, 4483, 17939] ⟨5424686902799, 13, [(2, 1), (29, 1), (1163, 1), (4483, 1), (17939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1163
    · exact prime_4483
    · exact prime_17939
  · decide +kernel

theorem prime_5428784672153 : Nat.Prime 5428784672153 := by
  apply nodeValid_prime [2, 59, 33427, 344083] ⟨5428784672153, 5, [(2, 3), (59, 1), (33427, 1), (344083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_33427
    · exact prime_344083
  · decide +kernel

theorem prime_5428784750713 : Nat.Prime 5428784750713 := by
  apply nodeValid_prime [2, 3, 226199364613] ⟨5428784750713, 15, [(2, 3), (3, 1), (226199364613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_226199364613
  · decide +kernel

theorem prime_5428784750839 : Nat.Prime 5428784750839 := by
  apply nodeValid_prime [2, 3, 19, 47620918867] ⟨5428784750839, 3, [(2, 1), (3, 1), (19, 1), (47620918867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_47620918867
  · decide +kernel

theorem prime_5432884443793 : Nat.Prime 5432884443793 := by
  apply nodeValid_prime [2, 3, 13, 4547, 638263] ⟨5432884443793, 5, [(2, 4), (3, 2), (13, 1), (4547, 1), (638263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4547
    · exact prime_638263
  · decide +kernel

theorem prime_5432884445203 : Nat.Prime 5432884445203 := by
  apply nodeValid_prime [2, 3, 29, 31, 1007208833] ⟨5432884445203, 2, [(2, 1), (3, 1), (29, 1), (31, 1), (1007208833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_31
    · exact prime_1007208833
  · decide +kernel

theorem prime_5432884566029 : Nat.Prime 5432884566029 := by
  apply nodeValid_prime [2, 23, 59053093109] ⟨5432884566029, 2, [(2, 2), (23, 1), (59053093109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59053093109
  · decide +kernel

theorem prime_5436986504647 : Nat.Prime 5436986504647 := by
  apply nodeValid_prime [2, 3, 223, 1997, 2034811] ⟨5436986504647, 3, [(2, 1), (3, 1), (223, 1), (1997, 1), (2034811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_1997
    · exact prime_2034811
  · decide +kernel

theorem prime_5436986506141 : Nat.Prime 5436986506141 := by
  apply nodeValid_prime [2, 3, 5, 7, 12945205967] ⟨5436986506141, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (12945205967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_12945205967
  · decide +kernel

theorem prime_5436986544839 : Nat.Prime 5436986544839 := by
  apply nodeValid_prime [2, 83, 137, 1567, 152567] ⟨5436986544839, 11, [(2, 1), (83, 1), (137, 1), (1567, 1), (152567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_137
    · exact prime_1567
    · exact prime_152567
  · decide +kernel

theorem prime_5441090604137 : Nat.Prime 5441090604137 := by
  apply nodeValid_prime [2, 11, 181, 16007, 21341] ⟨5441090604137, 3, [(2, 3), (11, 1), (181, 1), (16007, 1), (21341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_181
    · exact prime_16007
    · exact prime_21341
  · decide +kernel

theorem prime_5441090604413 : Nat.Prime 5441090604413 := by
  apply nodeValid_prime [2, 151, 9781, 921013] ⟨5441090604413, 2, [(2, 2), (151, 1), (9781, 1), (921013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_9781
    · exact prime_921013
  · decide +kernel

theorem prime_5441090609897 : Nat.Prime 5441090609897 := by
  apply nodeValid_prime [2, 23, 59, 587, 853843] ⟨5441090609897, 3, [(2, 3), (23, 1), (59, 1), (587, 1), (853843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59
    · exact prime_587
    · exact prime_853843
  · decide +kernel

theorem prime_5445196774453 : Nat.Prime 5445196774453 := by
  apply nodeValid_prime [2, 3, 130957, 1155001] ⟨5445196774453, 2, [(2, 2), (3, 2), (130957, 1), (1155001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_130957
    · exact prime_1155001
  · decide +kernel

theorem prime_5445196812743 : Nat.Prime 5445196812743 := by
  apply nodeValid_prime [2, 509, 5348916319] ⟨5445196812743, 5, [(2, 1), (509, 1), (5348916319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_509
    · exact prime_5348916319
  · decide +kernel

theorem prime_5445196813729 : Nat.Prime 5445196813729 := by
  apply nodeValid_prime [2, 3, 7, 137, 47969] ⟨5445196813729, 11, [(2, 5), (3, 3), (7, 1), (137, 2), (47969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
    · exact prime_47969
  · decide +kernel

theorem prime_5449305034549 : Nat.Prime 5449305034549 := by
  apply nodeValid_prime [2, 3, 151369584293] ⟨5449305034549, 2, [(2, 2), (3, 2), (151369584293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151369584293
  · decide +kernel

theorem prime_5449305088763 : Nat.Prime 5449305088763 := by
  apply nodeValid_prime [2, 2724652544381] ⟨5449305088763, 2, [(2, 1), (2724652544381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2724652544381
  · decide +kernel

theorem prime_5449305090259 : Nat.Prime 5449305090259 := by
  apply nodeValid_prime [2, 3, 42071, 2398637] ⟨5449305090259, 2, [(2, 1), (3, 3), (42071, 1), (2398637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42071
    · exact prime_2398637
  · decide +kernel

theorem prime_5453415338821 : Nat.Prime 5453415338821 := by
  apply nodeValid_prime [2, 3, 5, 199, 1951, 234103] ⟨5453415338821, 2, [(2, 2), (3, 1), (5, 1), (199, 1), (1951, 1), (234103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_1951
    · exact prime_234103
  · decide +kernel

theorem prime_5453415339941 : Nat.Prime 5453415339941 := by
  apply nodeValid_prime [2, 5, 23, 40973, 289343] ⟨5453415339941, 3, [(2, 2), (5, 1), (23, 1), (40973, 1), (289343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_40973
    · exact prime_289343
  · decide +kernel

theorem prime_5453415390923 : Nat.Prime 5453415390923 := by
  apply nodeValid_prime [2, 67, 97, 113, 1433, 2591] ⟨5453415390923, 2, [(2, 1), (67, 1), (97, 1), (113, 1), (1433, 1), (2591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_97
    · exact prime_113
    · exact prime_1433
    · exact prime_2591
  · decide +kernel

theorem prime_5457527825513 : Nat.Prime 5457527825513 := by
  apply nodeValid_prime [2, 7, 73, 131, 1455847] ⟨5457527825513, 3, [(2, 3), (7, 2), (73, 1), (131, 1), (1455847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_73
    · exact prime_131
    · exact prime_1455847
  · decide +kernel

theorem prime_5457527826623 : Nat.Prime 5457527826623 := by
  apply nodeValid_prime [2, 40039, 68152649] ⟨5457527826623, 5, [(2, 1), (40039, 1), (68152649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_40039
    · exact prime_68152649
  · decide +kernel

theorem prime_5457527844361 : Nat.Prime 5457527844361 := by
  apply nodeValid_prime [2, 3, 5, 23, 1977365161] ⟨5457527844361, 11, [(2, 3), (3, 1), (5, 1), (23, 1), (1977365161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1977365161
  · decide +kernel

end Sude.Lucas.Generated
