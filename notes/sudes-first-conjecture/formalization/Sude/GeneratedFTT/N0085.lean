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
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0084

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3533 : Nat.Prime 3533 := by
  apply nodeValid_prime [2, 883] ⟨3533, 2, [(2, 2), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_883
  · decide +kernel

theorem prime_7481 : Nat.Prime 7481 := by
  apply nodeValid_prime [2, 5, 11, 17] ⟨7481, 6, [(2, 3), (5, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_10039 : Nat.Prime 10039 := by
  apply nodeValid_prime [2, 3, 7, 239] ⟨10039, 3, [(2, 1), (3, 1), (7, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_239
  · decide +kernel

theorem prime_10949 : Nat.Prime 10949 := by
  apply nodeValid_prime [2, 7, 17, 23] ⟨10949, 2, [(2, 2), (7, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_12659 : Nat.Prime 12659 := by
  apply nodeValid_prime [2, 6329] ⟨12659, 2, [(2, 1), (6329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6329
  · decide +kernel

theorem prime_14821 : Nat.Prime 14821 := by
  apply nodeValid_prime [2, 3, 5, 13, 19] ⟨14821, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_20873 : Nat.Prime 20873 := by
  apply nodeValid_prime [2, 2609] ⟨20873, 3, [(2, 3), (2609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2609
  · decide +kernel

theorem prime_21991 : Nat.Prime 21991 := by
  apply nodeValid_prime [2, 3, 5, 733] ⟨21991, 3, [(2, 1), (3, 1), (5, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_733
  · decide +kernel

theorem prime_25589 : Nat.Prime 25589 := by
  apply nodeValid_prime [2, 6397] ⟨25589, 2, [(2, 2), (6397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6397
  · decide +kernel

theorem prime_32237 : Nat.Prime 32237 := by
  apply nodeValid_prime [2, 8059] ⟨32237, 2, [(2, 2), (8059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8059
  · decide +kernel

theorem prime_36847 : Nat.Prime 36847 := by
  apply nodeValid_prime [2, 3, 23, 89] ⟨36847, 3, [(2, 1), (3, 2), (23, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_89
  · decide +kernel

theorem prime_43721 : Nat.Prime 43721 := by
  apply nodeValid_prime [2, 5, 1093] ⟨43721, 3, [(2, 3), (5, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1093
  · decide +kernel

theorem prime_47087 : Nat.Prime 47087 := by
  apply nodeValid_prime [2, 13, 1811] ⟨47087, 5, [(2, 1), (13, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1811
  · decide +kernel

theorem prime_57179 : Nat.Prime 57179 := by
  apply nodeValid_prime [2, 11, 23, 113] ⟨57179, 2, [(2, 1), (11, 1), (23, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_113
  · decide +kernel

theorem prime_66301 : Nat.Prime 66301 := by
  apply nodeValid_prime [2, 3, 5, 13, 17] ⟨66301, 22, [(2, 2), (3, 1), (5, 2), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_67577 : Nat.Prime 67577 := by
  apply nodeValid_prime [2, 8447] ⟨67577, 3, [(2, 3), (8447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8447
  · decide +kernel

theorem prime_71809 : Nat.Prime 71809 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨71809, 7, [(2, 7), (3, 1), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_77573 : Nat.Prime 77573 := by
  apply nodeValid_prime [2, 11, 41, 43] ⟨77573, 2, [(2, 2), (11, 1), (41, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_43
  · decide +kernel

theorem prime_83059 : Nat.Prime 83059 := by
  apply nodeValid_prime [2, 3, 109, 127] ⟨83059, 2, [(2, 1), (3, 1), (109, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_127
  · decide +kernel

theorem prime_84793 : Nat.Prime 84793 := by
  apply nodeValid_prime [2, 3, 3533] ⟨84793, 5, [(2, 3), (3, 1), (3533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3533
  · decide +kernel

theorem prime_87443 : Nat.Prime 87443 := by
  apply nodeValid_prime [2, 43721] ⟨87443, 2, [(2, 1), (43721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43721
  · decide +kernel

theorem prime_109121 : Nat.Prime 109121 := by
  apply nodeValid_prime [2, 5, 11, 31] ⟨109121, 3, [(2, 6), (5, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_111487 : Nat.Prime 111487 := by
  apply nodeValid_prime [2, 3, 17, 1093] ⟨111487, 3, [(2, 1), (3, 1), (17, 1), (1093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1093
  · decide +kernel

theorem prime_113719 : Nat.Prime 113719 := by
  apply nodeValid_prime [2, 3, 11, 1723] ⟨113719, 6, [(2, 1), (3, 1), (11, 1), (1723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1723
  · decide +kernel

theorem prime_117659 : Nat.Prime 117659 := by
  apply nodeValid_prime [2, 89, 661] ⟨117659, 2, [(2, 1), (89, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_661
  · decide +kernel

theorem prime_126041 : Nat.Prime 126041 := by
  apply nodeValid_prime [2, 5, 23, 137] ⟨126041, 3, [(2, 3), (5, 1), (23, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_137
  · decide +kernel

theorem prime_147727 : Nat.Prime 147727 := by
  apply nodeValid_prime [2, 3, 29, 283] ⟨147727, 3, [(2, 1), (3, 2), (29, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_283
  · decide +kernel

theorem prime_148483 : Nat.Prime 148483 := by
  apply nodeValid_prime [2, 3, 73, 113] ⟨148483, 2, [(2, 1), (3, 2), (73, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_113
  · decide +kernel

theorem prime_148517 : Nat.Prime 148517 := by
  apply nodeValid_prime [2, 107, 347] ⟨148517, 2, [(2, 2), (107, 1), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_347
  · decide +kernel

theorem prime_167177 : Nat.Prime 167177 := by
  apply nodeValid_prime [2, 20897] ⟨167177, 3, [(2, 3), (20897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20897
  · decide +kernel

theorem prime_172157 : Nat.Prime 172157 := by
  apply nodeValid_prime [2, 193, 223] ⟨172157, 2, [(2, 2), (193, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_193
    · exact prime_223
  · decide +kernel

theorem prime_190391 : Nat.Prime 190391 := by
  apply nodeValid_prime [2, 5, 79, 241] ⟨190391, 11, [(2, 1), (5, 1), (79, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_241
  · decide +kernel

theorem prime_194141 : Nat.Prime 194141 := by
  apply nodeValid_prime [2, 5, 17, 571] ⟨194141, 2, [(2, 2), (5, 1), (17, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_571
  · decide +kernel

theorem prime_203789 : Nat.Prime 203789 := by
  apply nodeValid_prime [2, 13, 3919] ⟨203789, 2, [(2, 2), (13, 1), (3919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3919
  · decide +kernel

theorem prime_244939 : Nat.Prime 244939 := by
  apply nodeValid_prime [2, 3, 40823] ⟨244939, 2, [(2, 1), (3, 1), (40823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_40823
  · decide +kernel

theorem prime_264631 : Nat.Prime 264631 := by
  apply nodeValid_prime [2, 3, 5, 8821] ⟨264631, 15, [(2, 1), (3, 1), (5, 1), (8821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8821
  · decide +kernel

theorem prime_270241 : Nat.Prime 270241 := by
  apply nodeValid_prime [2, 3, 5, 563] ⟨270241, 7, [(2, 5), (3, 1), (5, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_563
  · decide +kernel

theorem prime_284041 : Nat.Prime 284041 := by
  apply nodeValid_prime [2, 3, 5, 263] ⟨284041, 19, [(2, 3), (3, 3), (5, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_287237 : Nat.Prime 287237 := by
  apply nodeValid_prime [2, 71809] ⟨287237, 2, [(2, 2), (71809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71809
  · decide +kernel

theorem prime_290327 : Nat.Prime 290327 := by
  apply nodeValid_prime [2, 17, 8539] ⟨290327, 5, [(2, 1), (17, 1), (8539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_8539
  · decide +kernel

theorem prime_314777 : Nat.Prime 314777 := by
  apply nodeValid_prime [2, 7, 11, 73] ⟨314777, 3, [(2, 3), (7, 2), (11, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_73
  · decide +kernel

theorem prime_329773 : Nat.Prime 329773 := by
  apply nodeValid_prime [2, 3, 27481] ⟨329773, 6, [(2, 2), (3, 1), (27481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27481
  · decide +kernel

theorem prime_337069 : Nat.Prime 337069 := by
  apply nodeValid_prime [2, 3, 3121] ⟨337069, 2, [(2, 2), (3, 3), (3121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3121
  · decide +kernel

theorem prime_407579 : Nat.Prime 407579 := by
  apply nodeValid_prime [2, 203789] ⟨407579, 2, [(2, 1), (203789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_203789
  · decide +kernel

theorem prime_483061 : Nat.Prime 483061 := by
  apply nodeValid_prime [2, 3, 5, 83, 97] ⟨483061, 2, [(2, 2), (3, 1), (5, 1), (83, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_83
    · exact prime_97
  · decide +kernel

theorem prime_551281 : Nat.Prime 551281 := by
  apply nodeValid_prime [2, 3, 5, 2297] ⟨551281, 14, [(2, 4), (3, 1), (5, 1), (2297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2297
  · decide +kernel

theorem prime_552239 : Nat.Prime 552239 := by
  apply nodeValid_prime [2, 71, 3889] ⟨552239, 7, [(2, 1), (71, 1), (3889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_3889
  · decide +kernel

theorem prime_625763 : Nat.Prime 625763 := by
  apply nodeValid_prime [2, 29, 10789] ⟨625763, 2, [(2, 1), (29, 1), (10789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_10789
  · decide +kernel

theorem prime_815159 : Nat.Prime 815159 := by
  apply nodeValid_prime [2, 407579] ⟨815159, 7, [(2, 1), (407579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_407579
  · decide +kernel

theorem prime_815231 : Nat.Prime 815231 := by
  apply nodeValid_prime [2, 5, 13, 6271] ⟨815231, 7, [(2, 1), (5, 1), (13, 1), (6271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_6271
  · decide +kernel

theorem prime_1032943 : Nat.Prime 1032943 := by
  apply nodeValid_prime [2, 3, 172157] ⟨1032943, 3, [(2, 1), (3, 1), (172157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_172157
  · decide +kernel

theorem prime_1396007 : Nat.Prime 1396007 := by
  apply nodeValid_prime [2, 17, 19, 2161] ⟨1396007, 5, [(2, 1), (17, 1), (19, 1), (2161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_2161
  · decide +kernel

theorem prime_1686071 : Nat.Prime 1686071 := by
  apply nodeValid_prime [2, 5, 139, 1213] ⟨1686071, 7, [(2, 1), (5, 1), (139, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_1213
  · decide +kernel

theorem prime_1736393 : Nat.Prime 1736393 := by
  apply nodeValid_prime [2, 7, 101, 307] ⟨1736393, 3, [(2, 3), (7, 1), (101, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_307
  · decide +kernel

theorem prime_2002799 : Nat.Prime 2002799 := by
  apply nodeValid_prime [2, 7, 29, 4933] ⟨2002799, 7, [(2, 1), (7, 1), (29, 1), (4933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_4933
  · decide +kernel

theorem prime_2172803 : Nat.Prime 2172803 := by
  apply nodeValid_prime [2, 19, 57179] ⟨2172803, 2, [(2, 1), (19, 1), (57179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_57179
  · decide +kernel

theorem prime_2434763 : Nat.Prime 2434763 := by
  apply nodeValid_prime [2, 11, 10061] ⟨2434763, 2, [(2, 1), (11, 2), (10061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_10061
  · decide +kernel

theorem prime_2758061 : Nat.Prime 2758061 := by
  apply nodeValid_prime [2, 5, 239, 577] ⟨2758061, 2, [(2, 2), (5, 1), (239, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
    · exact prime_577
  · decide +kernel

theorem prime_2790569 : Nat.Prime 2790569 := by
  apply nodeValid_prime [2, 11, 19, 1669] ⟨2790569, 3, [(2, 3), (11, 1), (19, 1), (1669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1669
  · decide +kernel

theorem prime_2940761 : Nat.Prime 2940761 := by
  apply nodeValid_prime [2, 5, 37, 1987] ⟨2940761, 6, [(2, 3), (5, 1), (37, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_1987
  · decide +kernel

theorem prime_3052249 : Nat.Prime 3052249 := by
  apply nodeValid_prime [2, 3, 17, 7481] ⟨3052249, 11, [(2, 3), (3, 1), (17, 1), (7481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_7481
  · decide +kernel

theorem prime_3109081 : Nat.Prime 3109081 := by
  apply nodeValid_prime [2, 3, 5, 13, 1993] ⟨3109081, 21, [(2, 3), (3, 1), (5, 1), (13, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_1993
  · decide +kernel

theorem prime_4244017 : Nat.Prime 4244017 := by
  apply nodeValid_prime [2, 3, 7, 17, 743] ⟨4244017, 15, [(2, 4), (3, 1), (7, 1), (17, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_743
  · decide +kernel

theorem prime_4494701 : Nat.Prime 4494701 := by
  apply nodeValid_prime [2, 5, 7, 6421] ⟨4494701, 2, [(2, 2), (5, 2), (7, 1), (6421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_6421
  · decide +kernel

theorem prime_5516123 : Nat.Prime 5516123 := by
  apply nodeValid_prime [2, 2758061] ⟨5516123, 2, [(2, 1), (2758061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2758061
  · decide +kernel

theorem prime_5881523 : Nat.Prime 5881523 := by
  apply nodeValid_prime [2, 2940761] ⟨5881523, 2, [(2, 1), (2940761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2940761
  · decide +kernel

theorem prime_5970511 : Nat.Prime 5970511 := by
  apply nodeValid_prime [2, 3, 5, 7, 13] ⟨5970511, 24, [(2, 1), (3, 8), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_7135169 : Nat.Prime 7135169 := by
  apply nodeValid_prime [2, 111487] ⟨7135169, 3, [(2, 6), (111487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_111487
  · decide +kernel

theorem prime_8898887 : Nat.Prime 8898887 := by
  apply nodeValid_prime [2, 41, 47, 2309] ⟨8898887, 5, [(2, 1), (41, 1), (47, 1), (2309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_47
    · exact prime_2309
  · decide +kernel

theorem prime_9164873 : Nat.Prime 9164873 := by
  apply nodeValid_prime [2, 409, 2801] ⟨9164873, 3, [(2, 3), (409, 1), (2801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_2801
  · decide +kernel

theorem prime_10963789 : Nat.Prime 10963789 := by
  apply nodeValid_prime [2, 3, 11, 83059] ⟨10963789, 13, [(2, 2), (3, 1), (11, 1), (83059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_83059
  · decide +kernel

theorem prime_12059189 : Nat.Prime 12059189 := by
  apply nodeValid_prime [2, 17, 37, 4793] ⟨12059189, 2, [(2, 2), (17, 1), (37, 1), (4793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_4793
  · decide +kernel

theorem prime_12352019 : Nat.Prime 12352019 := by
  apply nodeValid_prime [2, 7, 126041] ⟨12352019, 2, [(2, 1), (7, 2), (126041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_126041
  · decide +kernel

theorem prime_13771913 : Nat.Prime 13771913 := by
  apply nodeValid_prime [2, 7, 11, 79, 283] ⟨13771913, 3, [(2, 3), (7, 1), (11, 1), (79, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_79
    · exact prime_283
  · decide +kernel

theorem prime_14403973 : Nat.Prime 14403973 := by
  apply nodeValid_prime [2, 3, 11, 109121] ⟨14403973, 5, [(2, 2), (3, 1), (11, 1), (109121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_109121
  · decide +kernel

theorem prime_17219633 : Nat.Prime 17219633 := by
  apply nodeValid_prime [2, 31, 149, 233] ⟨17219633, 3, [(2, 4), (31, 1), (149, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_149
    · exact prime_233
  · decide +kernel

theorem prime_21939529 : Nat.Prime 21939529 := by
  apply nodeValid_prime [2, 3, 13, 19, 3701] ⟨21939529, 11, [(2, 3), (3, 1), (13, 1), (19, 1), (3701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_3701
  · decide +kernel

theorem prime_22791049 : Nat.Prime 22791049 := by
  apply nodeValid_prime [2, 3, 7, 135661] ⟨22791049, 44, [(2, 3), (3, 1), (7, 1), (135661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_135661
  · decide +kernel

theorem prime_22846921 : Nat.Prime 22846921 := by
  apply nodeValid_prime [2, 3, 5, 190391] ⟨22846921, 13, [(2, 3), (3, 1), (5, 1), (190391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_190391
  · decide +kernel

theorem prime_29978363 : Nat.Prime 29978363 := by
  apply nodeValid_prime [2, 37, 10949] ⟨29978363, 2, [(2, 1), (37, 2), (10949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_10949
  · decide +kernel

theorem prime_33486829 : Nat.Prime 33486829 := by
  apply nodeValid_prime [2, 3, 2790569] ⟨33486829, 2, [(2, 2), (3, 1), (2790569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2790569
  · decide +kernel

theorem prime_39127633 : Nat.Prime 39127633 := by
  apply nodeValid_prime [2, 3, 815159] ⟨39127633, 5, [(2, 4), (3, 1), (815159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_815159
  · decide +kernel

theorem prime_43673551 : Nat.Prime 43673551 := by
  apply nodeValid_prime [2, 3, 5, 23, 12659] ⟨43673551, 3, [(2, 1), (3, 1), (5, 2), (23, 1), (12659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_12659
  · decide +kernel

theorem prime_45411217 : Nat.Prime 45411217 := by
  apply nodeValid_prime [2, 3, 17, 19, 29, 101] ⟨45411217, 5, [(2, 4), (3, 1), (17, 1), (19, 1), (29, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_29
    · exact prime_101
  · decide +kernel

theorem prime_56734789 : Nat.Prime 56734789 := by
  apply nodeValid_prime [2, 3, 11, 29, 14821] ⟨56734789, 2, [(2, 2), (3, 1), (11, 1), (29, 1), (14821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_14821
  · decide +kernel

theorem prime_101416477 : Nat.Prime 101416477 := by
  apply nodeValid_prime [2, 3, 7, 23, 7499] ⟨101416477, 2, [(2, 2), (3, 1), (7, 2), (23, 1), (7499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_7499
  · decide +kernel

theorem prime_107176841 : Nat.Prime 107176841 := by
  apply nodeValid_prime [2, 5, 17, 277, 569] ⟨107176841, 3, [(2, 3), (5, 1), (17, 1), (277, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_277
    · exact prime_569
  · decide +kernel

theorem prime_114132341 : Nat.Prime 114132341 := by
  apply nodeValid_prime [2, 5, 7, 815231] ⟨114132341, 2, [(2, 2), (5, 1), (7, 1), (815231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_815231
  · decide +kernel

theorem prime_148124941 : Nat.Prime 148124941 := by
  apply nodeValid_prime [2, 3, 5, 67, 36847] ⟨148124941, 2, [(2, 2), (3, 1), (5, 1), (67, 1), (36847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_36847
  · decide +kernel

theorem prime_156422263 : Nat.Prime 156422263 := by
  apply nodeValid_prime [2, 3, 1249, 20873] ⟨156422263, 5, [(2, 1), (3, 1), (1249, 1), (20873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1249
    · exact prime_20873
  · decide +kernel

theorem prime_211358057 : Nat.Prime 211358057 := by
  apply nodeValid_prime [2, 7, 13, 290327] ⟨211358057, 5, [(2, 3), (7, 1), (13, 1), (290327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_290327
  · decide +kernel

theorem prime_222046031 : Nat.Prime 222046031 := by
  apply nodeValid_prime [2, 5, 4211, 5273] ⟨222046031, 7, [(2, 1), (5, 1), (4211, 1), (5273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4211
    · exact prime_5273
  · decide +kernel

theorem prime_226939157 : Nat.Prime 226939157 := by
  apply nodeValid_prime [2, 56734789] ⟨226939157, 2, [(2, 2), (56734789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56734789
  · decide +kernel

theorem prime_247023967 : Nat.Prime 247023967 := by
  apply nodeValid_prime [2, 3, 7, 5881523] ⟨247023967, 5, [(2, 1), (3, 1), (7, 1), (5881523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5881523
  · decide +kernel

theorem prime_249162203 : Nat.Prime 249162203 := by
  apply nodeValid_prime [2, 461, 270241] ⟨249162203, 2, [(2, 1), (461, 1), (270241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_461
    · exact prime_270241
  · decide +kernel

theorem prime_249856379 : Nat.Prime 249856379 := by
  apply nodeValid_prime [2, 17, 41, 151, 1187] ⟨249856379, 2, [(2, 1), (17, 1), (41, 1), (151, 1), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_41
    · exact prime_151
    · exact prime_1187
  · decide +kernel

theorem prime_278282087 : Nat.Prime 278282087 := by
  apply nodeValid_prime [2, 29, 71, 67577] ⟨278282087, 5, [(2, 1), (29, 1), (71, 1), (67577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_71
    · exact prime_67577
  · decide +kernel

theorem prime_293515273 : Nat.Prime 293515273 := by
  apply nodeValid_prime [2, 3, 53, 25639] ⟨293515273, 5, [(2, 3), (3, 3), (53, 1), (25639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_25639
  · decide +kernel

theorem prime_334868291 : Nat.Prime 334868291 := by
  apply nodeValid_prime [2, 5, 33486829] ⟨334868291, 2, [(2, 1), (5, 1), (33486829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33486829
  · decide +kernel

theorem prime_385299127 : Nat.Prime 385299127 := by
  apply nodeValid_prime [2, 3, 7135169] ⟨385299127, 3, [(2, 1), (3, 3), (7135169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7135169
  · decide +kernel

theorem prime_592006741 : Nat.Prime 592006741 := by
  apply nodeValid_prime [2, 3, 5, 13, 331, 2293] ⟨592006741, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (331, 1), (2293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_331
    · exact prime_2293
  · decide +kernel

theorem prime_643061047 : Nat.Prime 643061047 := by
  apply nodeValid_prime [2, 3, 107176841] ⟨643061047, 3, [(2, 1), (3, 1), (107176841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107176841
  · decide +kernel

theorem prime_732757847 : Nat.Prime 732757847 := by
  apply nodeValid_prime [2, 211, 1736393] ⟨732757847, 5, [(2, 1), (211, 1), (1736393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_1736393
  · decide +kernel

theorem prime_1092697981 : Nat.Prime 1092697981 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 79, 1103] ⟨1092697981, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (79, 1), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_79
    · exact prime_1103
  · decide +kernel

theorem prime_4345873409 : Nat.Prime 4345873409 := by
  apply nodeValid_prime [2, 4244017] ⟨4345873409, 3, [(2, 10), (4244017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4244017
  · decide +kernel

theorem prime_6390167633 : Nat.Prime 6390167633 := by
  apply nodeValid_prime [2, 29, 13771913] ⟨6390167633, 3, [(2, 4), (29, 1), (13771913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_13771913
  · decide +kernel

theorem prime_7629084457 : Nat.Prime 7629084457 := by
  apply nodeValid_prime [2, 3, 7, 45411217] ⟨7629084457, 10, [(2, 3), (3, 1), (7, 1), (45411217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_45411217
  · decide +kernel

theorem prime_8212513613 : Nat.Prime 8212513613 := by
  apply nodeValid_prime [2, 17, 193, 625763] ⟨8212513613, 2, [(2, 2), (17, 1), (193, 1), (625763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_193
    · exact prime_625763
  · decide +kernel

theorem prime_14266083079 : Nat.Prime 14266083079 := by
  apply nodeValid_prime [2, 3, 13, 719, 84793] ⟨14266083079, 3, [(2, 1), (3, 2), (13, 1), (719, 1), (84793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_719
    · exact prime_84793
  · decide +kernel

theorem prime_17296556353 : Nat.Prime 17296556353 := by
  apply nodeValid_prime [2, 3, 37, 2434763] ⟨17296556353, 5, [(2, 6), (3, 1), (37, 1), (2434763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2434763
  · decide +kernel

theorem prime_19040447479 : Nat.Prime 19040447479 := by
  apply nodeValid_prime [2, 3, 13, 41, 53, 112337] ⟨19040447479, 3, [(2, 1), (3, 1), (13, 1), (41, 1), (53, 1), (112337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41
    · exact prime_53
    · exact prime_112337
  · decide +kernel

theorem prime_38156985491 : Nat.Prime 38156985491 := by
  apply nodeValid_prime [2, 5, 13, 293515273] ⟨38156985491, 6, [(2, 1), (5, 1), (13, 1), (293515273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_293515273
  · decide +kernel

theorem prime_47696231003 : Nat.Prime 47696231003 := by
  apply nodeValid_prime [2, 7, 23, 148124941] ⟨47696231003, 2, [(2, 1), (7, 1), (23, 1), (148124941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_148124941
  · decide +kernel

theorem prime_95678285953 : Nat.Prime 95678285953 := by
  apply nodeValid_prime [2, 3, 249162203] ⟨95678285953, 7, [(2, 7), (3, 1), (249162203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_249162203
  · decide +kernel

theorem prime_125421707441 : Nat.Prime 125421707441 := by
  apply nodeValid_prime [2, 5, 103, 2939, 5179] ⟨125421707441, 3, [(2, 4), (5, 1), (103, 1), (2939, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_2939
    · exact prime_5179
  · decide +kernel

theorem prime_163366829849 : Nat.Prime 163366829849 := by
  apply nodeValid_prime [2, 53, 385299127] ⟨163366829849, 3, [(2, 3), (53, 1), (385299127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_385299127
  · decide +kernel

theorem prime_187944052733 : Nat.Prime 187944052733 := by
  apply nodeValid_prime [2, 43, 1092697981] ⟨187944052733, 2, [(2, 2), (43, 1), (1092697981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1092697981
  · decide +kernel

theorem prime_283048205681 : Nat.Prime 283048205681 := by
  apply nodeValid_prime [2, 5, 31, 114132341] ⟨283048205681, 6, [(2, 4), (5, 1), (31, 1), (114132341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_114132341
  · decide +kernel

theorem prime_572354772037 : Nat.Prime 572354772037 := by
  apply nodeValid_prime [2, 3, 47696231003] ⟨572354772037, 5, [(2, 2), (3, 1), (47696231003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47696231003
  · decide +kernel

theorem prime_573497671603 : Nat.Prime 573497671603 := by
  apply nodeValid_prime [2, 3, 23, 467, 8898887] ⟨573497671603, 5, [(2, 1), (3, 1), (23, 1), (467, 1), (8898887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_467
    · exact prime_8898887
  · decide +kernel

theorem prime_1129927086341 : Nat.Prime 1129927086341 := by
  apply nodeValid_prime [2, 5, 13, 4345873409] ⟨1129927086341, 2, [(2, 2), (5, 1), (13, 1), (4345873409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_4345873409
  · decide +kernel

theorem prime_2246296496029 : Nat.Prime 2246296496029 := by
  apply nodeValid_prime [2, 3, 13, 43, 334868291] ⟨2246296496029, 6, [(2, 2), (3, 1), (13, 1), (43, 1), (334868291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_43
    · exact prime_334868291
  · decide +kernel

theorem prime_2246296496573 : Nat.Prime 2246296496573 := by
  apply nodeValid_prime [2, 79, 101, 421, 167177] ⟨2246296496573, 2, [(2, 2), (79, 1), (101, 1), (421, 1), (167177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_101
    · exact prime_421
    · exact prime_167177
  · decide +kernel

theorem prime_2246296592833 : Nat.Prime 2246296592833 := by
  apply nodeValid_prime [2, 3, 17, 8731, 78823] ⟨2246296592833, 5, [(2, 6), (3, 1), (17, 1), (8731, 1), (78823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8731
    · exact prime_78823
  · decide +kernel

theorem prime_2248552325891 : Nat.Prime 2248552325891 := by
  apply nodeValid_prime [2, 5, 13, 17296556353] ⟨2248552325891, 2, [(2, 1), (5, 1), (13, 1), (17296556353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17296556353
  · decide +kernel

theorem prime_2248552326457 : Nat.Prime 2248552326457 := by
  apply nodeValid_prime [2, 3, 131, 10039, 23747] ⟨2248552326457, 5, [(2, 3), (3, 2), (131, 1), (10039, 1), (23747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_10039
    · exact prime_23747
  · decide +kernel

theorem prime_2248552342801 : Nat.Prime 2248552342801 := by
  apply nodeValid_prime [2, 3, 5, 431, 483061] ⟨2248552342801, 13, [(2, 4), (3, 3), (5, 2), (431, 1), (483061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_431
    · exact prime_483061
  · decide +kernel

theorem prime_2250809605769 : Nat.Prime 2250809605769 := by
  apply nodeValid_prime [2, 59, 2381, 2002799] ⟨2250809605769, 3, [(2, 3), (59, 1), (2381, 1), (2002799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2381
    · exact prime_2002799
  · decide +kernel

theorem prime_2250809606219 : Nat.Prime 2250809606219 := by
  apply nodeValid_prime [2, 179, 509, 12352019] ⟨2250809606219, 2, [(2, 1), (179, 1), (509, 1), (12352019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_509
    · exact prime_12352019
  · decide +kernel

theorem prime_2250809629283 : Nat.Prime 2250809629283 := by
  apply nodeValid_prime [2, 1901, 592006741] ⟨2250809629283, 2, [(2, 1), (1901, 1), (592006741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1901
    · exact prime_592006741
  · decide +kernel

theorem prime_2253068427943 : Nat.Prime 2253068427943 := by
  apply nodeValid_prime [2, 3, 419, 2539, 117659] ⟨2253068427943, 3, [(2, 1), (3, 2), (419, 1), (2539, 1), (117659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_419
    · exact prime_2539
    · exact prime_117659
  · decide +kernel

theorem prime_2253068430121 : Nat.Prime 2253068430121 := by
  apply nodeValid_prime [2, 3, 5, 32237, 194141] ⟨2253068430121, 7, [(2, 3), (3, 2), (5, 1), (32237, 1), (194141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_32237
    · exact prime_194141
  · decide +kernel

theorem prime_2253068453033 : Nat.Prime 2253068453033 := by
  apply nodeValid_prime [2, 2777, 101416477] ⟨2253068453033, 3, [(2, 3), (2777, 1), (101416477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2777
    · exact prime_101416477
  · decide +kernel

theorem prime_2255328631799 : Nat.Prime 2255328631799 := by
  apply nodeValid_prime [2, 11, 383, 3061, 87443] ⟨2255328631799, 11, [(2, 1), (11, 1), (383, 1), (3061, 1), (87443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_383
    · exact prime_3061
    · exact prime_87443
  · decide +kernel

theorem prime_2255328632797 : Nat.Prime 2255328632797 := by
  apply nodeValid_prime [2, 3, 187944052733] ⟨2255328632797, 5, [(2, 2), (3, 1), (187944052733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_187944052733
  · decide +kernel

theorem prime_2255328818711 : Nat.Prime 2255328818711 := by
  apply nodeValid_prime [2, 5, 11, 83, 247023967] ⟨2255328818711, 11, [(2, 1), (5, 1), (11, 1), (83, 1), (247023967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_83
    · exact prime_247023967
  · decide +kernel

theorem prime_2257590728671 : Nat.Prime 2257590728671 := by
  apply nodeValid_prime [2, 3, 5, 67, 14479, 77573] ⟨2257590728671, 13, [(2, 1), (3, 1), (5, 1), (67, 1), (14479, 1), (77573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_14479
    · exact prime_77573
  · decide +kernel

theorem prime_2257590733837 : Nat.Prime 2257590733837 := by
  apply nodeValid_prime [2, 3, 829, 226939157] ⟨2257590733837, 2, [(2, 2), (3, 1), (829, 1), (226939157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_829
    · exact prime_226939157
  · decide +kernel

theorem prime_2257590733939 : Nat.Prime 2257590733939 := by
  apply nodeValid_prime [2, 3, 125421707441] ⟨2257590733939, 3, [(2, 1), (3, 2), (125421707441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_125421707441
  · decide +kernel

theorem prime_2259854172683 : Nat.Prime 2259854172683 := by
  apply nodeValid_prime [2, 1129927086341] ⟨2259854172683, 2, [(2, 1), (1129927086341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1129927086341
  · decide +kernel

theorem prime_2259854179337 : Nat.Prime 2259854179337 := by
  apply nodeValid_prime [2, 13, 29, 241, 3109081] ⟨2259854179337, 3, [(2, 3), (13, 1), (29, 1), (241, 1), (3109081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_241
    · exact prime_3109081
  · decide +kernel

theorem prime_2259854179393 : Nat.Prime 2259854179393 := by
  apply nodeValid_prime [2, 3, 5417, 2172803] ⟨2259854179393, 5, [(2, 6), (3, 1), (5417, 1), (2172803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5417
    · exact prime_2172803
  · decide +kernel

theorem prime_2262119148703 : Nat.Prime 2262119148703 := by
  apply nodeValid_prime [2, 3, 7, 31, 97, 5970511] ⟨2262119148703, 3, [(2, 1), (3, 2), (7, 1), (31, 1), (97, 1), (5970511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_97
    · exact prime_5970511
  · decide +kernel

theorem prime_2262119342053 : Nat.Prime 2262119342053 := by
  apply nodeValid_prime [2, 3, 37, 223, 22846921] ⟨2262119342053, 5, [(2, 2), (3, 1), (37, 1), (223, 1), (22846921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_223
    · exact prime_22846921
  · decide +kernel

theorem prime_2262119342083 : Nat.Prime 2262119342083 := by
  apply nodeValid_prime [2, 3, 59, 6390167633] ⟨2262119342083, 2, [(2, 1), (3, 1), (59, 1), (6390167633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_6390167633
  · decide +kernel

theorem prime_2264385645449 : Nat.Prime 2264385645449 := by
  apply nodeValid_prime [2, 283048205681] ⟨2264385645449, 3, [(2, 3), (283048205681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_283048205681
  · decide +kernel

theorem prime_2264385645559 : Nat.Prime 2264385645559 := by
  apply nodeValid_prime [2, 3, 73, 6067, 284041] ⟨2264385645559, 6, [(2, 1), (3, 2), (73, 1), (6067, 1), (284041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_6067
    · exact prime_284041
  · decide +kernel

theorem prime_2264385670843 : Nat.Prime 2264385670843 := by
  apply nodeValid_prime [2, 3, 12589, 29978363] ⟨2264385670843, 2, [(2, 1), (3, 1), (12589, 1), (29978363, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12589
    · exact prime_29978363
  · decide +kernel

theorem prime_2266653737861 : Nat.Prime 2266653737861 := by
  apply nodeValid_prime [2, 5, 10337, 10963789] ⟨2266653737861, 3, [(2, 2), (5, 1), (10337, 1), (10963789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10337
    · exact prime_10963789
  · decide +kernel

theorem prime_2266653757063 : Nat.Prime 2266653757063 := by
  apply nodeValid_prime [2, 3, 2693, 6379, 21991] ⟨2266653757063, 5, [(2, 1), (3, 1), (2693, 1), (6379, 1), (21991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2693
    · exact prime_6379
    · exact prime_21991
  · decide +kernel

theorem prime_2266653757189 : Nat.Prime 2266653757189 := by
  apply nodeValid_prime [2, 3, 23, 8212513613] ⟨2266653757189, 2, [(2, 2), (3, 1), (23, 1), (8212513613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_8212513613
  · decide +kernel

theorem prime_2268923341967 : Nat.Prime 2268923341967 := by
  apply nodeValid_prime [2, 199, 5519, 1032943] ⟨2268923341967, 5, [(2, 1), (199, 1), (5519, 1), (1032943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_5519
    · exact prime_1032943
  · decide +kernel

theorem prime_2268923352389 : Nat.Prime 2268923352389 := by
  apply nodeValid_prime [2, 7, 11, 137, 1013, 7583] ⟨2268923352389, 2, [(2, 2), (7, 2), (11, 1), (137, 1), (1013, 1), (7583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_137
    · exact prime_1013
    · exact prime_7583
  · decide +kernel

theorem prime_2268923353703 : Nat.Prime 2268923353703 := by
  apply nodeValid_prime [2, 181, 25589, 244939] ⟨2268923353703, 5, [(2, 1), (181, 1), (25589, 1), (244939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_25589
    · exact prime_244939
  · decide +kernel

theorem prime_2271194439779 : Nat.Prime 2271194439779 := by
  apply nodeValid_prime [2, 11, 19, 9839, 552239] ⟨2271194439779, 2, [(2, 1), (11, 1), (19, 1), (9839, 1), (552239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_9839
    · exact prime_552239
  · decide +kernel

theorem prime_2271194440297 : Nat.Prime 2271194440297 := by
  apply nodeValid_prime [2, 3, 137, 4651, 148517] ⟨2271194440297, 7, [(2, 3), (3, 1), (137, 1), (4651, 1), (148517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_4651
    · exact prime_148517
  · decide +kernel

theorem prime_2271194485111 : Nat.Prime 2271194485111 := by
  apply nodeValid_prime [2, 3, 5, 101, 249856379] ⟨2271194485111, 3, [(2, 1), (3, 2), (5, 1), (101, 1), (249856379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_249856379
  · decide +kernel

theorem prime_2273467168187 : Nat.Prime 2273467168187 := by
  apply nodeValid_prime [2, 149, 7629084457] ⟨2273467168187, 2, [(2, 1), (149, 1), (7629084457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_7629084457
  · decide +kernel

theorem prime_2273467199851 : Nat.Prime 2273467199851 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 47, 1396007] ⟨2273467199851, 11, [(2, 1), (3, 2), (5, 2), (7, 1), (11, 1), (47, 1), (1396007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_47
    · exact prime_1396007
  · decide +kernel

theorem prime_2273467200229 : Nat.Prime 2273467200229 := by
  apply nodeValid_prime [2, 3, 7, 157, 5857, 9811] ⟨2273467200229, 2, [(2, 2), (3, 2), (7, 1), (157, 1), (5857, 1), (9811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_157
    · exact prime_5857
    · exact prime_9811
  · decide +kernel

theorem prime_2275741388819 : Nat.Prime 2275741388819 := by
  apply nodeValid_prime [2, 127, 33857, 264631] ⟨2275741388819, 2, [(2, 1), (127, 1), (33857, 1), (264631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_33857
    · exact prime_264631
  · decide +kernel

theorem prime_2275741390547 : Nat.Prime 2275741390547 := by
  apply nodeValid_prime [2, 13, 2237, 39127633] ⟨2275741390547, 2, [(2, 1), (13, 1), (2237, 1), (39127633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2237
    · exact prime_39127633
  · decide +kernel

theorem prime_2275741395509 : Nat.Prime 2275741395509 := by
  apply nodeValid_prime [2, 7, 1861, 43673551] ⟨2275741395509, 2, [(2, 2), (7, 1), (1861, 1), (43673551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1861
    · exact prime_43673551
  · decide +kernel

theorem prime_2278017137897 : Nat.Prime 2278017137897 := by
  apply nodeValid_prime [2, 53, 373, 14403973] ⟨2278017137897, 3, [(2, 3), (53, 1), (373, 1), (14403973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_373
    · exact prime_14403973
  · decide +kernel

theorem prime_2278017138347 : Nat.Prime 2278017138347 := by
  apply nodeValid_prime [2, 17, 317, 211358057] ⟨2278017138347, 2, [(2, 1), (17, 1), (317, 1), (211358057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_317
    · exact prime_211358057
  · decide +kernel

theorem prime_2278017164183 : Nat.Prime 2278017164183 := by
  apply nodeValid_prime [2, 4093, 278282087] ⟨2278017164183, 5, [(2, 1), (4093, 1), (278282087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4093
    · exact prime_278282087
  · decide +kernel

theorem prime_2280294466451 : Nat.Prime 2280294466451 := by
  apply nodeValid_prime [2, 5, 7, 11, 13, 6491, 7019] ⟨2280294466451, 2, [(2, 1), (5, 2), (7, 1), (11, 1), (13, 1), (6491, 1), (7019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_6491
    · exact prime_7019
  · decide +kernel

theorem prime_2280294472037 : Nat.Prime 2280294472037 := by
  apply nodeValid_prime [2, 7, 147727, 551281] ⟨2280294472037, 2, [(2, 2), (7, 1), (147727, 1), (551281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_147727
    · exact prime_551281
  · decide +kernel

theorem prime_2280294472663 : Nat.Prime 2280294472663 := by
  apply nodeValid_prime [2, 3, 197, 643061047] ⟨2280294472663, 3, [(2, 1), (3, 2), (197, 1), (643061047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_643061047
  · decide +kernel

theorem prime_2282573292133 : Nat.Prime 2282573292133 := by
  apply nodeValid_prime [2, 3, 7, 19, 4243, 337069] ⟨2282573292133, 5, [(2, 2), (3, 1), (7, 1), (19, 1), (4243, 1), (337069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_4243
    · exact prime_337069
  · decide +kernel

theorem prime_2282573292641 : Nat.Prime 2282573292641 := by
  apply nodeValid_prime [2, 5, 14266083079] ⟨2282573292641, 3, [(2, 5), (5, 1), (14266083079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_14266083079
  · decide +kernel

theorem prime_2282573308247 : Nat.Prime 2282573308247 := by
  apply nodeValid_prime [2, 7, 11, 47087, 314777] ⟨2282573308247, 7, [(2, 1), (7, 1), (11, 1), (47087, 1), (314777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_47087
    · exact prime_314777
  · decide +kernel

theorem prime_2284853658229 : Nat.Prime 2284853658229 := by
  apply nodeValid_prime [2, 3, 61, 5231, 66301] ⟨2284853658229, 11, [(2, 2), (3, 3), (61, 1), (5231, 1), (66301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_5231
    · exact prime_66301
  · decide +kernel

theorem prime_2284853658991 : Nat.Prime 2284853658991 := by
  apply nodeValid_prime [2, 3, 5, 7, 222046031] ⟨2284853658991, 3, [(2, 1), (3, 1), (5, 1), (7, 3), (222046031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_222046031
  · decide +kernel

theorem prime_2284853697481 : Nat.Prime 2284853697481 := by
  apply nodeValid_prime [2, 3, 5, 19040447479] ⟨2284853697481, 17, [(2, 3), (3, 1), (5, 1), (19040447479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19040447479
  · decide +kernel

theorem prime_2287135617887 : Nat.Prime 2287135617887 := by
  apply nodeValid_prime [2, 7, 163366829849] ⟨2287135617887, 5, [(2, 1), (7, 1), (163366829849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163366829849
  · decide +kernel

theorem prime_2287135618051 : Nat.Prime 2287135618051 := by
  apply nodeValid_prime [2, 3, 5, 29, 3541, 148483] ⟨2287135618051, 2, [(2, 1), (3, 1), (5, 2), (29, 1), (3541, 1), (148483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_3541
    · exact prime_148483
  · decide +kernel

theorem prime_2287135638673 : Nat.Prime 2287135638673 := by
  apply nodeValid_prime [2, 3, 67, 233, 3052249] ⟨2287135638673, 5, [(2, 4), (3, 1), (67, 1), (233, 1), (3052249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_233
    · exact prime_3052249
  · decide +kernel

theorem prime_2289419085883 : Nat.Prime 2289419085883 := by
  apply nodeValid_prime [2, 3, 22159, 17219633] ⟨2289419085883, 2, [(2, 1), (3, 1), (22159, 1), (17219633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22159
    · exact prime_17219633
  · decide +kernel

theorem prime_2289419088149 : Nat.Prime 2289419088149 := by
  apply nodeValid_prime [2, 572354772037] ⟨2289419088149, 2, [(2, 2), (572354772037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_572354772037
  · decide +kernel

theorem prime_2289419129461 : Nat.Prime 2289419129461 := by
  apply nodeValid_prime [2, 3, 5, 38156985491] ⟨2289419129461, 14, [(2, 2), (3, 1), (5, 1), (38156985491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_38156985491
  · decide +kernel

theorem prime_2291704159183 : Nat.Prime 2291704159183 := by
  apply nodeValid_prime [2, 3, 19, 1667, 12059189] ⟨2291704159183, 3, [(2, 1), (3, 1), (19, 1), (1667, 1), (12059189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1667
    · exact prime_12059189
  · decide +kernel

theorem prime_2291704209469 : Nat.Prime 2291704209469 := by
  apply nodeValid_prime [2, 3, 4721, 4494701] ⟨2291704209469, 2, [(2, 2), (3, 3), (4721, 1), (4494701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4721
    · exact prime_4494701
  · decide +kernel

theorem prime_2291704211107 : Nat.Prime 2291704211107 := by
  apply nodeValid_prime [2, 3, 811, 6791, 23117] ⟨2291704211107, 2, [(2, 1), (3, 2), (811, 1), (6791, 1), (23117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
    · exact prime_6791
    · exact prime_23117
  · decide +kernel

theorem prime_2293990686257 : Nat.Prime 2293990686257 := by
  apply nodeValid_prime [2, 409, 1063, 329773] ⟨2293990686257, 3, [(2, 4), (409, 1), (1063, 1), (329773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_1063
    · exact prime_329773
  · decide +kernel

theorem prime_2293990686413 : Nat.Prime 2293990686413 := by
  apply nodeValid_prime [2, 573497671603] ⟨2293990686413, 2, [(2, 2), (573497671603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_573497671603
  · decide +kernel

theorem prime_2293990725749 : Nat.Prime 2293990725749 := by
  apply nodeValid_prime [2, 443, 4507, 287237] ⟨2293990725749, 2, [(2, 2), (443, 1), (4507, 1), (287237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_4507
    · exact prime_287237
  · decide +kernel

theorem prime_2296278820841 : Nat.Prime 2296278820841 := by
  apply nodeValid_prime [2, 5, 367, 156422263] ⟨2296278820841, 3, [(2, 3), (5, 1), (367, 1), (156422263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_367
    · exact prime_156422263
  · decide +kernel

theorem prime_2296278862873 : Nat.Prime 2296278862873 := by
  apply nodeValid_prime [2, 3, 95678285953] ⟨2296278862873, 5, [(2, 3), (3, 1), (95678285953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_95678285953
  · decide +kernel

theorem prime_2296278863257 : Nat.Prime 2296278863257 := by
  apply nodeValid_prime [2, 3, 7, 89, 21939529] ⟨2296278863257, 5, [(2, 3), (3, 1), (7, 2), (89, 1), (21939529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_89
    · exact prime_21939529
  · decide +kernel

theorem prime_2298568454101 : Nat.Prime 2298568454101 := by
  apply nodeValid_prime [2, 3, 5, 463, 5516123] ⟨2298568454101, 18, [(2, 2), (3, 2), (5, 2), (463, 1), (5516123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_463
    · exact prime_5516123
  · decide +kernel

theorem prime_2298568455847 : Nat.Prime 2298568455847 := by
  apply nodeValid_prime [2, 3, 13, 431, 22791049] ⟨2298568455847, 3, [(2, 1), (3, 2), (13, 1), (431, 1), (22791049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_431
    · exact prime_22791049
  · decide +kernel

theorem prime_2298568456361 : Nat.Prime 2298568456361 := by
  apply nodeValid_prime [2, 5, 11, 31, 229, 239, 3079] ⟨2298568456361, 3, [(2, 3), (5, 1), (11, 1), (31, 1), (229, 1), (239, 1), (3079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_229
    · exact prime_239
    · exact prime_3079
  · decide +kernel

theorem prime_2300859639581 : Nat.Prime 2300859639581 := by
  apply nodeValid_prime [2, 5, 157, 732757847] ⟨2300859639581, 2, [(2, 2), (5, 1), (157, 1), (732757847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_732757847
  · decide +kernel

theorem prime_2300859696397 : Nat.Prime 2300859696397 := by
  apply nodeValid_prime [2, 3, 20921, 9164873] ⟨2300859696397, 2, [(2, 2), (3, 1), (20921, 1), (9164873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20921
    · exact prime_9164873
  · decide +kernel

theorem prime_2300859696589 : Nat.Prime 2300859696589 := by
  apply nodeValid_prime [2, 3, 113719, 1686071] ⟨2300859696589, 2, [(2, 2), (3, 1), (113719, 1), (1686071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113719
    · exact prime_1686071
  · decide +kernel

end Sude.Lucas.Generated
