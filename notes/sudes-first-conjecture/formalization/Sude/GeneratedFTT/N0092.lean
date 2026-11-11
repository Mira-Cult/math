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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0059
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0079
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0089

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9859 : Nat.Prime 9859 := by
  apply nodeValid_prime [2, 3, 31, 53] ⟨9859, 2, [(2, 1), (3, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_10429 : Nat.Prime 10429 := by
  apply nodeValid_prime [2, 3, 11, 79] ⟨10429, 7, [(2, 2), (3, 1), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_17477 : Nat.Prime 17477 := by
  apply nodeValid_prime [2, 17, 257] ⟨17477, 2, [(2, 2), (17, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_257
  · decide +kernel

theorem prime_22067 : Nat.Prime 22067 := by
  apply nodeValid_prime [2, 11, 17, 59] ⟨22067, 2, [(2, 1), (11, 1), (17, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_59
  · decide +kernel

theorem prime_23609 : Nat.Prime 23609 := by
  apply nodeValid_prime [2, 13, 227] ⟨23609, 6, [(2, 3), (13, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_227
  · decide +kernel

theorem prime_26321 : Nat.Prime 26321 := by
  apply nodeValid_prime [2, 5, 7, 47] ⟨26321, 3, [(2, 4), (5, 1), (7, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
  · decide +kernel

theorem prime_30881 : Nat.Prime 30881 := by
  apply nodeValid_prime [2, 5, 193] ⟨30881, 3, [(2, 5), (5, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
  · decide +kernel

theorem prime_33413 : Nat.Prime 33413 := by
  apply nodeValid_prime [2, 8353] ⟨33413, 2, [(2, 2), (8353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_8353
  · decide +kernel

theorem prime_35291 : Nat.Prime 35291 := by
  apply nodeValid_prime [2, 5, 3529] ⟨35291, 2, [(2, 1), (5, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3529
  · decide +kernel

theorem prime_45677 : Nat.Prime 45677 := by
  apply nodeValid_prime [2, 19, 601] ⟨45677, 2, [(2, 2), (19, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_601
  · decide +kernel

theorem prime_46919 : Nat.Prime 46919 := by
  apply nodeValid_prime [2, 23459] ⟨46919, 11, [(2, 1), (23459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23459
  · decide +kernel

theorem prime_65239 : Nat.Prime 65239 := by
  apply nodeValid_prime [2, 3, 83, 131] ⟨65239, 3, [(2, 1), (3, 1), (83, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_131
  · decide +kernel

theorem prime_85819 : Nat.Prime 85819 := by
  apply nodeValid_prime [2, 3, 14303] ⟨85819, 2, [(2, 1), (3, 1), (14303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14303
  · decide +kernel

theorem prime_90841 : Nat.Prime 90841 := by
  apply nodeValid_prime [2, 3, 5, 757] ⟨90841, 17, [(2, 3), (3, 1), (5, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_757
  · decide +kernel

theorem prime_91459 : Nat.Prime 91459 := by
  apply nodeValid_prime [2, 3, 5081] ⟨91459, 2, [(2, 1), (3, 2), (5081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5081
  · decide +kernel

theorem prime_98041 : Nat.Prime 98041 := by
  apply nodeValid_prime [2, 3, 5, 19, 43] ⟨98041, 13, [(2, 3), (3, 1), (5, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_110533 : Nat.Prime 110533 := by
  apply nodeValid_prime [2, 3, 61, 151] ⟨110533, 5, [(2, 2), (3, 1), (61, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_151
  · decide +kernel

theorem prime_118169 : Nat.Prime 118169 := by
  apply nodeValid_prime [2, 14771] ⟨118169, 3, [(2, 3), (14771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14771
  · decide +kernel

theorem prime_125863 : Nat.Prime 125863 := by
  apply nodeValid_prime [2, 3, 11, 1907] ⟨125863, 3, [(2, 1), (3, 1), (11, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1907
  · decide +kernel

theorem prime_128189 : Nat.Prime 128189 := by
  apply nodeValid_prime [2, 73, 439] ⟨128189, 2, [(2, 2), (73, 1), (439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_439
  · decide +kernel

theorem prime_173357 : Nat.Prime 173357 := by
  apply nodeValid_prime [2, 19, 2281] ⟨173357, 2, [(2, 2), (19, 1), (2281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2281
  · decide +kernel

theorem prime_199807 : Nat.Prime 199807 := by
  apply nodeValid_prime [2, 3, 33301] ⟨199807, 3, [(2, 1), (3, 1), (33301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33301
  · decide +kernel

theorem prime_211747 : Nat.Prime 211747 := by
  apply nodeValid_prime [2, 3, 35291] ⟨211747, 2, [(2, 1), (3, 1), (35291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35291
  · decide +kernel

theorem prime_235523 : Nat.Prime 235523 := by
  apply nodeValid_prime [2, 7, 16823] ⟨235523, 2, [(2, 1), (7, 1), (16823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_16823
  · decide +kernel

theorem prime_257867 : Nat.Prime 257867 := by
  apply nodeValid_prime [2, 7, 113, 163] ⟨257867, 2, [(2, 1), (7, 1), (113, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_163
  · decide +kernel

theorem prime_265961 : Nat.Prime 265961 := by
  apply nodeValid_prime [2, 5, 61, 109] ⟨265961, 3, [(2, 3), (5, 1), (61, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_109
  · decide +kernel

theorem prime_300221 : Nat.Prime 300221 := by
  apply nodeValid_prime [2, 5, 17, 883] ⟨300221, 2, [(2, 2), (5, 1), (17, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_883
  · decide +kernel

theorem prime_333131 : Nat.Prime 333131 := by
  apply nodeValid_prime [2, 5, 7, 4759] ⟨333131, 2, [(2, 1), (5, 1), (7, 1), (4759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_4759
  · decide +kernel

theorem prime_339557 : Nat.Prime 339557 := by
  apply nodeValid_prime [2, 7, 67, 181] ⟨339557, 2, [(2, 2), (7, 1), (67, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_181
  · decide +kernel

theorem prime_359299 : Nat.Prime 359299 := by
  apply nodeValid_prime [2, 3, 19961] ⟨359299, 3, [(2, 1), (3, 2), (19961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19961
  · decide +kernel

theorem prime_365837 : Nat.Prime 365837 := by
  apply nodeValid_prime [2, 91459] ⟨365837, 2, [(2, 2), (91459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_91459
  · decide +kernel

theorem prime_383489 : Nat.Prime 383489 := by
  apply nodeValid_prime [2, 7, 107] ⟨383489, 3, [(2, 9), (7, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
  · decide +kernel

theorem prime_402691 : Nat.Prime 402691 := by
  apply nodeValid_prime [2, 3, 5, 31, 433] ⟨402691, 7, [(2, 1), (3, 1), (5, 1), (31, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_433
  · decide +kernel

theorem prime_463189 : Nat.Prime 463189 := by
  apply nodeValid_prime [2, 3, 11, 29] ⟨463189, 6, [(2, 2), (3, 1), (11, 3), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_493777 : Nat.Prime 493777 := by
  apply nodeValid_prime [2, 3, 127] ⟨493777, 5, [(2, 4), (3, 5), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
  · decide +kernel

theorem prime_555073 : Nat.Prime 555073 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨555073, 17, [(2, 6), (3, 1), (7, 2), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_574183 : Nat.Prime 574183 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨574183, 3, [(2, 1), (3, 3), (7, 3), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_619057 : Nat.Prime 619057 := by
  apply nodeValid_prime [2, 3, 1433] ⟨619057, 5, [(2, 4), (3, 3), (1433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1433
  · decide +kernel

theorem prime_752033 : Nat.Prime 752033 := by
  apply nodeValid_prime [2, 71, 331] ⟨752033, 3, [(2, 5), (71, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_331
  · decide +kernel

theorem prime_1070497 : Nat.Prime 1070497 := by
  apply nodeValid_prime [2, 3, 7, 59] ⟨1070497, 5, [(2, 5), (3, 4), (7, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
  · decide +kernel

theorem prime_1195489 : Nat.Prime 1195489 := by
  apply nodeValid_prime [2, 3, 7, 593] ⟨1195489, 37, [(2, 5), (3, 2), (7, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_593
  · decide +kernel

theorem prime_1504067 : Nat.Prime 1504067 := by
  apply nodeValid_prime [2, 752033] ⟨1504067, 2, [(2, 1), (752033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_752033
  · decide +kernel

theorem prime_1895599 : Nat.Prime 1895599 := by
  apply nodeValid_prime [2, 3, 53, 1987] ⟨1895599, 6, [(2, 1), (3, 2), (53, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_1987
  · decide +kernel

theorem prime_2017817 : Nat.Prime 2017817 := by
  apply nodeValid_prime [2, 53, 4759] ⟨2017817, 3, [(2, 3), (53, 1), (4759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_4759
  · decide +kernel

theorem prime_2220293 : Nat.Prime 2220293 := by
  apply nodeValid_prime [2, 555073] ⟨2220293, 2, [(2, 2), (555073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_555073
  · decide +kernel

theorem prime_2416147 : Nat.Prime 2416147 := by
  apply nodeValid_prime [2, 3, 402691] ⟨2416147, 3, [(2, 1), (3, 1), (402691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_402691
  · decide +kernel

theorem prime_2540641 : Nat.Prime 2540641 := by
  apply nodeValid_prime [2, 3, 5, 67, 79] ⟨2540641, 7, [(2, 5), (3, 1), (5, 1), (67, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_79
  · decide +kernel

theorem prime_2716457 : Nat.Prime 2716457 := by
  apply nodeValid_prime [2, 339557] ⟨2716457, 3, [(2, 3), (339557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_339557
  · decide +kernel

theorem prime_3191533 : Nat.Prime 3191533 := by
  apply nodeValid_prime [2, 3, 265961] ⟨3191533, 2, [(2, 2), (3, 1), (265961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_265961
  · decide +kernel

theorem prime_3197401 : Nat.Prime 3197401 := by
  apply nodeValid_prime [2, 3, 5, 73] ⟨3197401, 17, [(2, 3), (3, 1), (5, 2), (73, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_4252847 : Nat.Prime 4252847 := by
  apply nodeValid_prime [2, 13, 19, 8609] ⟨4252847, 10, [(2, 1), (13, 1), (19, 1), (8609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_8609
  · decide +kernel

theorem prime_4461671 : Nat.Prime 4461671 := by
  apply nodeValid_prime [2, 5, 173, 2579] ⟨4461671, 7, [(2, 1), (5, 1), (173, 1), (2579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_2579
  · decide +kernel

theorem prime_4642387 : Nat.Prime 4642387 := by
  apply nodeValid_prime [2, 3, 7, 110533] ⟨4642387, 5, [(2, 1), (3, 1), (7, 1), (110533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_110533
  · decide +kernel

theorem prime_6282071 : Nat.Prime 6282071 := by
  apply nodeValid_prime [2, 5, 628207] ⟨6282071, 11, [(2, 1), (5, 1), (628207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_628207
  · decide +kernel

theorem prime_6519871 : Nat.Prime 6519871 := by
  apply nodeValid_prime [2, 3, 5, 7, 79, 131] ⟨6519871, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (79, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_79
    · exact prime_131
  · decide +kernel

theorem prime_7029731 : Nat.Prime 7029731 := by
  apply nodeValid_prime [2, 5, 113, 6221] ⟨7029731, 2, [(2, 1), (5, 1), (113, 1), (6221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
    · exact prime_6221
  · decide +kernel

theorem prime_7196011 : Nat.Prime 7196011 := by
  apply nodeValid_prime [2, 3, 5, 23, 10429] ⟨7196011, 2, [(2, 1), (3, 1), (5, 1), (23, 1), (10429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_10429
  · decide +kernel

theorem prime_7260067 : Nat.Prime 7260067 := by
  apply nodeValid_prime [2, 3, 11, 37, 991] ⟨7260067, 3, [(2, 1), (3, 2), (11, 1), (37, 1), (991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_991
  · decide +kernel

theorem prime_8395951 : Nat.Prime 8395951 := by
  apply nodeValid_prime [2, 3, 5, 223, 251] ⟨8395951, 3, [(2, 1), (3, 1), (5, 2), (223, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
    · exact prime_251
  · decide +kernel

theorem prime_9767161 : Nat.Prime 9767161 := by
  apply nodeValid_prime [2, 3, 5, 13, 2087] ⟨9767161, 7, [(2, 3), (3, 2), (5, 1), (13, 1), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_2087
  · decide +kernel

theorem prime_12564143 : Nat.Prime 12564143 := by
  apply nodeValid_prime [2, 6282071] ⟨12564143, 5, [(2, 1), (6282071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6282071
  · decide +kernel

theorem prime_14780357 : Nat.Prime 14780357 := by
  apply nodeValid_prime [2, 3695089] ⟨14780357, 2, [(2, 2), (3695089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3695089
  · decide +kernel

theorem prime_17748007 : Nat.Prime 17748007 := by
  apply nodeValid_prime [2, 3, 113, 26177] ⟨17748007, 3, [(2, 1), (3, 1), (113, 1), (26177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_26177
  · decide +kernel

theorem prime_18613703 : Nat.Prime 18613703 := by
  apply nodeValid_prime [2, 31, 300221] ⟨18613703, 5, [(2, 1), (31, 1), (300221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_300221
  · decide +kernel

theorem prime_21056939 : Nat.Prime 21056939 := by
  apply nodeValid_prime [2, 7, 1504067] ⟨21056939, 2, [(2, 1), (7, 1), (1504067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1504067
  · decide +kernel

theorem prime_25270967 : Nat.Prime 25270967 := by
  apply nodeValid_prime [2, 7, 257867] ⟨25270967, 5, [(2, 1), (7, 2), (257867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_257867
  · decide +kernel

theorem prime_25819793 : Nat.Prime 25819793 := by
  apply nodeValid_prime [2, 151, 10687] ⟨25819793, 3, [(2, 4), (151, 1), (10687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_10687
  · decide +kernel

theorem prime_26138659 : Nat.Prime 26138659 := by
  apply nodeValid_prime [2, 3, 7, 13, 977] ⟨26138659, 2, [(2, 1), (3, 1), (7, 3), (13, 1), (977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_977
  · decide +kernel

theorem prime_31394159 : Nat.Prime 31394159 := by
  apply nodeValid_prime [2, 823, 19073] ⟨31394159, 11, [(2, 1), (823, 1), (19073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_823
    · exact prime_19073
  · decide +kernel

theorem prime_33954131 : Nat.Prime 33954131 := by
  apply nodeValid_prime [2, 5, 7, 485059] ⟨33954131, 2, [(2, 1), (5, 1), (7, 1), (485059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_485059
  · decide +kernel

theorem prime_35034941 : Nat.Prime 35034941 := by
  apply nodeValid_prime [2, 5, 409, 4283] ⟨35034941, 2, [(2, 2), (5, 1), (409, 1), (4283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
    · exact prime_4283
  · decide +kernel

theorem prime_53227393 : Nat.Prime 53227393 := by
  apply nodeValid_prime [2, 3, 97, 1429] ⟨53227393, 5, [(2, 7), (3, 1), (97, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1429
  · decide +kernel

theorem prime_56867971 : Nat.Prime 56867971 := by
  apply nodeValid_prime [2, 3, 5, 1895599] ⟨56867971, 2, [(2, 1), (3, 1), (5, 1), (1895599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1895599
  · decide +kernel

theorem prime_66569089 : Nat.Prime 66569089 := by
  apply nodeValid_prime [2, 3, 173357] ⟨66569089, 7, [(2, 7), (3, 1), (173357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173357
  · decide +kernel

theorem prime_78810877 : Nat.Prime 78810877 := by
  apply nodeValid_prime [2, 3, 223, 9817] ⟨78810877, 2, [(2, 2), (3, 2), (223, 1), (9817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_9817
  · decide +kernel

theorem prime_79425239 : Nat.Prime 79425239 := by
  apply nodeValid_prime [2, 1361, 29179] ⟨79425239, 11, [(2, 1), (1361, 1), (29179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1361
    · exact prime_29179
  · decide +kernel

theorem prime_80310079 : Nat.Prime 80310079 := by
  apply nodeValid_prime [2, 3, 4461671] ⟨80310079, 3, [(2, 1), (3, 2), (4461671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4461671
  · decide +kernel

theorem prime_82148999 : Nat.Prime 82148999 := by
  apply nodeValid_prime [2, 17, 2416147] ⟨82148999, 7, [(2, 1), (17, 1), (2416147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2416147
  · decide +kernel

theorem prime_82789241 : Nat.Prime 82789241 := by
  apply nodeValid_prime [2, 5, 157, 13183] ⟨82789241, 3, [(2, 3), (5, 1), (157, 1), (13183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_13183
  · decide +kernel

theorem prime_94070281 : Nat.Prime 94070281 := by
  apply nodeValid_prime [2, 3, 5, 37, 21187] ⟨94070281, 11, [(2, 3), (3, 1), (5, 1), (37, 1), (21187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_21187
  · decide +kernel

theorem prime_112067173 : Nat.Prime 112067173 := by
  apply nodeValid_prime [2, 3, 7, 271, 547] ⟨112067173, 5, [(2, 2), (3, 3), (7, 1), (271, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_271
    · exact prime_547
  · decide +kernel

theorem prime_123947093 : Nat.Prime 123947093 := by
  apply nodeValid_prime [2, 23, 823, 1637] ⟨123947093, 2, [(2, 2), (23, 1), (823, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_823
    · exact prime_1637
  · decide +kernel

theorem prime_171070301 : Nat.Prime 171070301 := by
  apply nodeValid_prime [2, 5, 19, 179, 503] ⟨171070301, 3, [(2, 2), (5, 2), (19, 1), (179, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_179
    · exact prime_503
  · decide +kernel

theorem prime_203281877 : Nat.Prime 203281877 := by
  apply nodeValid_prime [2, 7, 7260067] ⟨203281877, 2, [(2, 2), (7, 1), (7260067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7260067
  · decide +kernel

theorem prime_271633049 : Nat.Prime 271633049 := by
  apply nodeValid_prime [2, 33954131] ⟨271633049, 3, [(2, 3), (33954131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33954131
  · decide +kernel

theorem prime_312722257 : Nat.Prime 312722257 := by
  apply nodeValid_prime [2, 3, 7, 11, 211, 401] ⟨312722257, 10, [(2, 4), (3, 1), (7, 1), (11, 1), (211, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_211
    · exact prime_401
  · decide +kernel

theorem prime_319364359 : Nat.Prime 319364359 := by
  apply nodeValid_prime [2, 3, 53227393] ⟨319364359, 3, [(2, 1), (3, 1), (53227393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53227393
  · decide +kernel

theorem prime_343339583 : Nat.Prime 343339583 := by
  apply nodeValid_prime [2, 17, 103, 98041] ⟨343339583, 5, [(2, 1), (17, 1), (103, 1), (98041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_103
    · exact prime_98041
  · decide +kernel

theorem prime_543266099 : Nat.Prime 543266099 := by
  apply nodeValid_prime [2, 271633049] ⟨543266099, 2, [(2, 1), (271633049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_271633049
  · decide +kernel

theorem prime_572791937 : Nat.Prime 572791937 := by
  apply nodeValid_prime [2, 19, 235523] ⟨572791937, 3, [(2, 7), (19, 1), (235523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_235523
  · decide +kernel

theorem prime_730760579 : Nat.Prime 730760579 := by
  apply nodeValid_prime [2, 2903, 125863] ⟨730760579, 2, [(2, 1), (2903, 1), (125863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2903
    · exact prime_125863
  · decide +kernel

theorem prime_1486594327 : Nat.Prime 1486594327 := by
  apply nodeValid_prime [2, 3, 7, 59, 113, 5309] ⟨1486594327, 3, [(2, 1), (3, 1), (7, 1), (59, 1), (113, 1), (5309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_113
    · exact prime_5309
  · decide +kernel

theorem prime_1563780263 : Nat.Prime 1563780263 := by
  apply nodeValid_prime [2, 11, 41, 61, 97, 293] ⟨1563780263, 5, [(2, 1), (11, 1), (41, 1), (61, 1), (97, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_61
    · exact prime_97
    · exact prime_293
  · decide +kernel

theorem prime_1658309701 : Nat.Prime 1658309701 := by
  apply nodeValid_prime [2, 3, 5, 179, 30881] ⟨1658309701, 18, [(2, 2), (3, 1), (5, 2), (179, 1), (30881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_30881
  · decide +kernel

theorem prime_2086040417 : Nat.Prime 2086040417 := by
  apply nodeValid_prime [2, 1951, 33413] ⟨2086040417, 3, [(2, 5), (1951, 1), (33413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1951
    · exact prime_33413
  · decide +kernel

theorem prime_4940693767 : Nat.Prime 4940693767 := by
  apply nodeValid_prime [2, 3, 19, 41, 67, 1753] ⟨4940693767, 3, [(2, 1), (3, 3), (19, 1), (41, 1), (67, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
    · exact prime_67
    · exact prime_1753
  · decide +kernel

theorem prime_8260224857 : Nat.Prime 8260224857 := by
  apply nodeValid_prime [2, 13, 79425239] ⟨8260224857, 3, [(2, 3), (13, 1), (79425239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79425239
  · decide +kernel

theorem prime_14865943271 : Nat.Prime 14865943271 := by
  apply nodeValid_prime [2, 5, 1486594327] ⟨14865943271, 7, [(2, 1), (5, 1), (1486594327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1486594327
  · decide +kernel

theorem prime_14950426691 : Nat.Prime 14950426691 := by
  apply nodeValid_prime [2, 5, 71, 21056939] ⟨14950426691, 2, [(2, 1), (5, 1), (71, 1), (21056939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_71
    · exact prime_21056939
  · decide +kernel

theorem prime_19762775069 : Nat.Prime 19762775069 := by
  apply nodeValid_prime [2, 4940693767] ⟨19762775069, 2, [(2, 2), (4940693767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4940693767
  · decide +kernel

theorem prime_30426876517 : Nat.Prime 30426876517 := by
  apply nodeValid_prime [2, 3, 7057, 359299] ⟨30426876517, 2, [(2, 2), (3, 1), (7057, 1), (359299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7057
    · exact prime_359299
  · decide +kernel

theorem prime_37684475819 : Nat.Prime 37684475819 := by
  apply nodeValid_prime [2, 11, 2767, 619057] ⟨37684475819, 2, [(2, 1), (11, 1), (2767, 1), (619057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2767
    · exact prime_619057
  · decide +kernel

theorem prime_44753197583 : Nat.Prime 44753197583 := by
  apply nodeValid_prime [2, 20903, 1070497] ⟨44753197583, 5, [(2, 1), (20903, 1), (1070497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_20903
    · exact prime_1070497
  · decide +kernel

theorem prime_44965594319 : Nat.Prime 44965594319 := by
  apply nodeValid_prime [2, 239, 94070281] ⟨44965594319, 7, [(2, 1), (239, 1), (94070281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_94070281
  · decide +kernel

theorem prime_53348379719 : Nat.Prime 53348379719 := by
  apply nodeValid_prime [2, 10499, 2540641] ⟨53348379719, 13, [(2, 1), (10499, 1), (2540641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_10499
    · exact prime_2540641
  · decide +kernel

theorem prime_66939128341 : Nat.Prime 66939128341 := by
  apply nodeValid_prime [2, 3, 5, 7, 349, 65239] ⟨66939128341, 10, [(2, 2), (3, 1), (5, 1), (7, 2), (349, 1), (65239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_349
    · exact prime_65239
  · decide +kernel

theorem prime_71402164709 : Nat.Prime 71402164709 := by
  apply nodeValid_prime [2, 7, 137, 18613703] ⟨71402164709, 2, [(2, 2), (7, 1), (137, 1), (18613703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_137
    · exact prime_18613703
  · decide +kernel

theorem prime_75226674023 : Nat.Prime 75226674023 := by
  apply nodeValid_prime [2, 3851, 9767161] ⟨75226674023, 5, [(2, 1), (3851, 1), (9767161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3851
    · exact prime_9767161
  · decide +kernel

theorem prime_89931188639 : Nat.Prime 89931188639 := by
  apply nodeValid_prime [2, 44965594319] ⟨89931188639, 13, [(2, 1), (44965594319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44965594319
  · decide +kernel

theorem prime_90101490767 : Nat.Prime 90101490767 := by
  apply nodeValid_prime [2, 7, 163, 631, 1277] ⟨90101490767, 5, [(2, 1), (7, 3), (163, 1), (631, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_163
    · exact prime_631
    · exact prime_1277
  · decide +kernel

theorem prime_135792293837 : Nat.Prime 135792293837 := by
  apply nodeValid_prime [2, 167, 203281877] ⟨135792293837, 2, [(2, 2), (167, 1), (203281877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_203281877
  · decide +kernel

theorem prime_149460251461 : Nat.Prime 149460251461 := by
  apply nodeValid_prime [2, 3, 5, 13, 107, 199, 8999] ⟨149460251461, 10, [(2, 2), (3, 1), (5, 1), (13, 1), (107, 1), (199, 1), (8999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_107
    · exact prime_199
    · exact prime_8999
  · decide +kernel

theorem prime_167030550877 : Nat.Prime 167030550877 := by
  apply nodeValid_prime [2, 3, 7, 47, 127, 333131] ⟨167030550877, 2, [(2, 2), (3, 1), (7, 1), (47, 1), (127, 1), (333131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_127
    · exact prime_333131
  · decide +kernel

theorem prime_226106863603 : Nat.Prime 226106863603 := by
  apply nodeValid_prime [2, 3, 8861, 4252847] ⟨226106863603, 2, [(2, 1), (3, 1), (8861, 1), (4252847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8861
    · exact prime_4252847
  · decide +kernel

theorem prime_268010570041 : Nat.Prime 268010570041 := by
  apply nodeValid_prime [2, 3, 5, 23, 37, 2624467] ⟨268010570041, 26, [(2, 3), (3, 1), (5, 1), (23, 1), (37, 1), (2624467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_37
    · exact prime_2624467
  · decide +kernel

theorem prime_1337513093201 : Nat.Prime 1337513093201 := by
  apply nodeValid_prime [2, 5, 2797, 1195489] ⟨1337513093201, 3, [(2, 4), (5, 2), (2797, 1), (1195489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2797
    · exact prime_1195489
  · decide +kernel

theorem prime_1343868704693 : Nat.Prime 1343868704693 := by
  apply nodeValid_prime [2, 17, 19762775069] ⟨1343868704693, 2, [(2, 2), (17, 1), (19762775069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19762775069
  · decide +kernel

theorem prime_2664886519927 : Nat.Prime 2664886519927 := by
  apply nodeValid_prime [2, 3, 37, 661, 2017817] ⟨2664886519927, 3, [(2, 1), (3, 3), (37, 1), (661, 1), (2017817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_661
    · exact prime_2017817
  · decide +kernel

theorem prime_2664886655941 : Nat.Prime 2664886655941 := by
  apply nodeValid_prime [2, 3, 5, 103, 751, 574183] ⟨2664886655941, 2, [(2, 2), (3, 1), (5, 1), (103, 1), (751, 1), (574183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
    · exact prime_751
    · exact prime_574183
  · decide +kernel

theorem prime_2667418963907 : Nat.Prime 2667418963907 := by
  apply nodeValid_prime [2, 16607, 80310079] ⟨2667418963907, 2, [(2, 1), (16607, 1), (80310079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_16607
    · exact prime_80310079
  · decide +kernel

theorem prime_2667418964059 : Nat.Prime 2667418964059 := by
  apply nodeValid_prime [2, 3, 37, 677, 17748007] ⟨2667418964059, 2, [(2, 1), (3, 1), (37, 1), (677, 1), (17748007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_677
    · exact prime_17748007
  · decide +kernel

theorem prime_2667418985951 : Nat.Prime 2667418985951 := by
  apply nodeValid_prime [2, 5, 53348379719] ⟨2667418985951, 11, [(2, 1), (5, 2), (53348379719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_53348379719
  · decide +kernel

theorem prime_2669953021613 : Nat.Prime 2669953021613 := by
  apply nodeValid_prime [2, 37, 271, 66569089] ⟨2669953021613, 2, [(2, 2), (37, 1), (271, 1), (66569089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_271
    · exact prime_66569089
  · decide +kernel

theorem prime_2669953022251 : Nat.Prime 2669953022251 := by
  apply nodeValid_prime [2, 3, 5, 43, 82789241] ⟨2669953022251, 2, [(2, 1), (3, 1), (5, 3), (43, 1), (82789241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_82789241
  · decide +kernel

theorem prime_2669953085323 : Nat.Prime 2669953085323 := by
  apply nodeValid_prime [2, 3, 131, 353, 9622909] ⟨2669953085323, 22, [(2, 1), (3, 1), (131, 1), (353, 1), (9622909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
    · exact prime_353
    · exact prime_9622909
  · decide +kernel

theorem prime_2672488814033 : Nat.Prime 2672488814033 := by
  apply nodeValid_prime [2, 167030550877] ⟨2672488814033, 3, [(2, 4), (167030550877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_167030550877
  · decide +kernel

theorem prime_2672488822321 : Nat.Prime 2672488822321 := by
  apply nodeValid_prime [2, 3, 5, 9679, 383489] ⟨2672488822321, 7, [(2, 4), (3, 2), (5, 1), (9679, 1), (383489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9679
    · exact prime_383489
  · decide +kernel

theorem prime_2672488823713 : Nat.Prime 2672488823713 := by
  apply nodeValid_prime [2, 3, 61, 20681, 22067] ⟨2672488823713, 5, [(2, 5), (3, 1), (61, 1), (20681, 1), (22067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_20681
    · exact prime_22067
  · decide +kernel

theorem prime_2675026161127 : Nat.Prime 2675026161127 := by
  apply nodeValid_prime [2, 3, 11, 109, 123947093] ⟨2675026161127, 3, [(2, 1), (3, 2), (11, 1), (109, 1), (123947093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_109
    · exact prime_123947093
  · decide +kernel

theorem prime_2675026186379 : Nat.Prime 2675026186379 := by
  apply nodeValid_prime [2, 7, 13, 47, 312722257] ⟨2675026186379, 2, [(2, 1), (7, 1), (13, 1), (47, 1), (312722257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_47
    · exact prime_312722257
  · decide +kernel

theorem prime_2675026186403 : Nat.Prime 2675026186403 := by
  apply nodeValid_prime [2, 1337513093201] ⟨2675026186403, 2, [(2, 1), (1337513093201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1337513093201
  · decide +kernel

theorem prime_2677565133497 : Nat.Prime 2677565133497 := by
  apply nodeValid_prime [2, 11, 30426876517] ⟨2677565133497, 3, [(2, 3), (11, 1), (30426876517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_30426876517
  · decide +kernel

theorem prime_2677565133641 : Nat.Prime 2677565133641 := by
  apply nodeValid_prime [2, 5, 66939128341] ⟨2677565133641, 3, [(2, 3), (5, 1), (66939128341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_66939128341
  · decide +kernel

theorem prime_2677565135873 : Nat.Prime 2677565135873 := by
  apply nodeValid_prime [2, 11, 47, 73, 79, 877] ⟨2677565135873, 5, [(2, 10), (11, 1), (47, 1), (73, 1), (79, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_47
    · exact prime_73
    · exact prime_79
    · exact prime_877
  · decide +kernel

theorem prime_2680105700411 : Nat.Prime 2680105700411 := by
  apply nodeValid_prime [2, 5, 268010570041] ⟨2680105700411, 2, [(2, 1), (5, 1), (268010570041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_268010570041
  · decide +kernel

theorem prime_2680105700729 : Nat.Prime 2680105700729 := by
  apply nodeValid_prime [2, 1049, 319364359] ⟨2680105700729, 3, [(2, 3), (1049, 1), (319364359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1049
    · exact prime_319364359
  · decide +kernel

theorem prime_2680105753667 : Nat.Prime 2680105753667 := by
  apply nodeValid_prime [2, 11, 89, 251, 1217, 4481] ⟨2680105753667, 2, [(2, 1), (11, 1), (89, 1), (251, 1), (1217, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
    · exact prime_251
    · exact prime_1217
    · exact prime_4481
  · decide +kernel

theorem prime_2682647976179 : Nat.Prime 2682647976179 := by
  apply nodeValid_prime [2, 493777, 2716457] ⟨2682647976179, 2, [(2, 1), (493777, 1), (2716457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_493777
    · exact prime_2716457
  · decide +kernel

theorem prime_2682647976263 : Nat.Prime 2682647976263 := by
  apply nodeValid_prime [2, 643, 2086040417] ⟨2682647976263, 5, [(2, 1), (643, 1), (2086040417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_643
    · exact prime_2086040417
  · decide +kernel

theorem prime_2682647996863 : Nat.Prime 2682647996863 := by
  apply nodeValid_prime [2, 3, 823, 543266099] ⟨2682647996863, 3, [(2, 1), (3, 1), (823, 1), (543266099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_823
    · exact prime_543266099
  · decide +kernel

theorem prime_2685191854679 : Nat.Prime 2685191854679 := by
  apply nodeValid_prime [2, 23609, 56867971] ⟨2685191854679, 11, [(2, 1), (23609, 1), (56867971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23609
    · exact prime_56867971
  · decide +kernel

theorem prime_2685191854981 : Nat.Prime 2685191854981 := by
  apply nodeValid_prime [2, 3, 5, 44753197583] ⟨2685191854981, 2, [(2, 2), (3, 1), (5, 1), (44753197583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_44753197583
  · decide +kernel

theorem prime_2685191869553 : Nat.Prime 2685191869553 := by
  apply nodeValid_prime [2, 29, 229, 25270967] ⟨2685191869553, 5, [(2, 4), (29, 1), (229, 1), (25270967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_229
    · exact prime_25270967
  · decide +kernel

theorem prime_2687737375753 : Nat.Prime 2687737375753 := by
  apply nodeValid_prime [2, 3, 11, 13, 37, 233, 90841] ⟨2687737375753, 15, [(2, 3), (3, 1), (11, 1), (13, 1), (37, 1), (233, 1), (90841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_37
    · exact prime_233
    · exact prime_90841
  · decide +kernel

theorem prime_2687737409387 : Nat.Prime 2687737409387 := by
  apply nodeValid_prime [2, 1343868704693] ⟨2687737409387, 2, [(2, 1), (1343868704693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1343868704693
  · decide +kernel

theorem prime_2687737409563 : Nat.Prime 2687737409563 := by
  apply nodeValid_prime [2, 3, 613, 730760579] ⟨2687737409563, 3, [(2, 1), (3, 1), (613, 1), (730760579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_730760579
  · decide +kernel

theorem prime_2690284526299 : Nat.Prime 2690284526299 := by
  apply nodeValid_prime [2, 3, 149460251461] ⟨2690284526299, 3, [(2, 1), (3, 2), (149460251461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149460251461
  · decide +kernel

theorem prime_2690284555039 : Nat.Prime 2690284555039 := by
  apply nodeValid_prime [2, 3, 4001, 112067173] ⟨2690284555039, 3, [(2, 1), (3, 1), (4001, 1), (112067173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4001
    · exact prime_112067173
  · decide +kernel

theorem prime_2690284555733 : Nat.Prime 2690284555733 := by
  apply nodeValid_prime [2, 199, 269, 12564143] ⟨2690284555733, 2, [(2, 2), (199, 1), (269, 1), (12564143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_269
    · exact prime_12564143
  · decide +kernel

theorem prime_2692833303383 : Nat.Prime 2692833303383 := by
  apply nodeValid_prime [2, 163, 8260224857] ⟨2692833303383, 5, [(2, 1), (163, 1), (8260224857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_8260224857
  · decide +kernel

theorem prime_2692833363641 : Nat.Prime 2692833363641 := by
  apply nodeValid_prime [2, 5, 7, 61, 6691, 23563] ⟨2692833363641, 6, [(2, 3), (5, 1), (7, 1), (61, 1), (6691, 1), (23563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_6691
    · exact prime_23563
  · decide +kernel

theorem prime_2692833364231 : Nat.Prime 2692833364231 := by
  apply nodeValid_prime [2, 3, 5, 10691, 8395951] ⟨2692833364231, 3, [(2, 1), (3, 1), (5, 1), (10691, 1), (8395951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_10691
    · exact prime_8395951
  · decide +kernel

theorem prime_2695383662557 : Nat.Prime 2695383662557 := by
  apply nodeValid_prime [2, 3, 13, 101, 171070301] ⟨2695383662557, 6, [(2, 2), (3, 1), (13, 1), (101, 1), (171070301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_101
    · exact prime_171070301
  · decide +kernel

theorem prime_2695383662887 : Nat.Prime 2695383662887 := by
  apply nodeValid_prime [2, 3, 46919, 3191533] ⟨2695383662887, 3, [(2, 1), (3, 2), (46919, 1), (3191533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_46919
    · exact prime_3191533
  · decide +kernel

theorem prime_2695383715201 : Nat.Prime 2695383715201 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 1031, 1303] ⟨2695383715201, 13, [(2, 7), (3, 1), (5, 2), (11, 1), (19, 1), (1031, 1), (1303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_1031
    · exact prime_1303
  · decide +kernel

theorem prime_2697935659171 : Nat.Prime 2697935659171 := by
  apply nodeValid_prime [2, 3, 5, 89931188639] ⟨2697935659171, 3, [(2, 1), (3, 1), (5, 1), (89931188639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89931188639
  · decide +kernel

theorem prime_2697935659543 : Nat.Prime 2697935659543 := by
  apply nodeValid_prime [2, 3, 79, 97, 6519871] ⟨2697935659543, 3, [(2, 1), (3, 3), (79, 1), (97, 1), (6519871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_97
    · exact prime_6519871
  · decide +kernel

theorem prime_2697935751919 : Nat.Prime 2697935751919 := by
  apply nodeValid_prime [2, 3, 11, 17, 19, 2220293] ⟨2697935751919, 3, [(2, 1), (3, 2), (11, 1), (17, 1), (19, 2), (2220293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_2220293
  · decide +kernel

theorem prime_2700489415927 : Nat.Prime 2700489415927 := by
  apply nodeValid_prime [2, 3, 67, 257, 26138659] ⟨2700489415927, 3, [(2, 1), (3, 1), (67, 1), (257, 1), (26138659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_257
    · exact prime_26138659
  · decide +kernel

theorem prime_2700489466453 : Nat.Prime 2700489466453 := by
  apply nodeValid_prime [2, 3, 17, 37, 2791, 128189] ⟨2700489466453, 6, [(2, 2), (3, 1), (17, 1), (37, 1), (2791, 1), (128189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_2791
    · exact prime_128189
  · decide +kernel

theorem prime_2700489466757 : Nat.Prime 2700489466757 := by
  apply nodeValid_prime [2, 45677, 14780357] ⟨2700489466757, 2, [(2, 2), (45677, 1), (14780357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_45677
    · exact prime_14780357
  · decide +kernel

theorem prime_2703044723011 : Nat.Prime 2703044723011 := by
  apply nodeValid_prime [2, 3, 5, 90101490767] ⟨2703044723011, 10, [(2, 1), (3, 1), (5, 1), (90101490767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_90101490767
  · decide +kernel

theorem prime_2703044812631 : Nat.Prime 2703044812631 := by
  apply nodeValid_prime [2, 5, 163, 1658309701] ⟨2703044812631, 7, [(2, 1), (5, 1), (163, 1), (1658309701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_1658309701
  · decide +kernel

theorem prime_2705601675323 : Nat.Prime 2705601675323 := by
  apply nodeValid_prime [2, 7, 13, 14865943271] ⟨2705601675323, 2, [(2, 1), (7, 1), (13, 1), (14865943271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_14865943271
  · decide +kernel

theorem prime_2705601713123 : Nat.Prime 2705601713123 := by
  apply nodeValid_prime [2, 7, 11, 71, 4957, 49919] ⟨2705601713123, 6, [(2, 1), (7, 1), (11, 1), (71, 1), (4957, 1), (49919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_71
    · exact prime_4957
    · exact prime_49919
  · decide +kernel

theorem prime_2705601713149 : Nat.Prime 2705601713149 := by
  apply nodeValid_prime [2, 3, 16189, 4642387] ⟨2705601713149, 2, [(2, 2), (3, 2), (16189, 1), (4642387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16189
    · exact prime_4642387
  · decide +kernel

theorem prime_2708160264829 : Nat.Prime 2708160264829 := by
  apply nodeValid_prime [2, 3, 75226674023] ⟨2708160264829, 6, [(2, 2), (3, 2), (75226674023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_75226674023
  · decide +kernel

theorem prime_2708160278137 : Nat.Prime 2708160278137 := by
  apply nodeValid_prime [2, 3, 197, 572791937] ⟨2708160278137, 10, [(2, 3), (3, 1), (197, 1), (572791937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_572791937
  · decide +kernel

theorem prime_2708160278189 : Nat.Prime 2708160278189 := by
  apply nodeValid_prime [2, 211747, 3197401] ⟨2708160278189, 2, [(2, 2), (211747, 1), (3197401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211747
    · exact prime_3197401
  · decide +kernel

theorem prime_2710720468681 : Nat.Prime 2710720468681 := by
  apply nodeValid_prime [2, 3, 5, 7, 8821, 365837] ⟨2710720468681, 19, [(2, 3), (3, 1), (5, 1), (7, 1), (8821, 1), (365837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_8821
    · exact prime_365837
  · decide +kernel

theorem prime_2710720470397 : Nat.Prime 2710720470397 := by
  apply nodeValid_prime [2, 3, 433, 6079, 85819] ⟨2710720470397, 5, [(2, 2), (3, 1), (433, 1), (6079, 1), (85819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_433
    · exact prime_6079
    · exact prime_85819
  · decide +kernel

theorem prime_2710720495253 : Nat.Prime 2710720495253 := by
  apply nodeValid_prime [2, 7, 11, 97, 9203, 9859] ⟨2710720495253, 3, [(2, 2), (7, 1), (11, 1), (97, 1), (9203, 1), (9859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_97
    · exact prime_9203
    · exact prime_9859
  · decide +kernel

theorem prime_2713282258943 : Nat.Prime 2713282258943 := by
  apply nodeValid_prime [2, 19, 71402164709] ⟨2713282258943, 5, [(2, 1), (19, 1), (71402164709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71402164709
  · decide +kernel

theorem prime_2713282258969 : Nat.Prime 2713282258969 := by
  apply nodeValid_prime [2, 3, 37684475819] ⟨2713282258969, 11, [(2, 3), (3, 2), (37684475819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37684475819
  · decide +kernel

theorem prime_2713282363237 : Nat.Prime 2713282363237 := by
  apply nodeValid_prime [2, 3, 226106863603] ⟨2713282363237, 2, [(2, 2), (3, 1), (226106863603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_226106863603
  · decide +kernel

theorem prime_2715845876741 : Nat.Prime 2715845876741 := by
  apply nodeValid_prime [2, 5, 135792293837] ⟨2715845876741, 2, [(2, 2), (5, 1), (135792293837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_135792293837
  · decide +kernel

theorem prime_2715845906773 : Nat.Prime 2715845906773 := by
  apply nodeValid_prime [2, 3, 89, 31394159] ⟨2715845906773, 5, [(2, 2), (3, 5), (89, 1), (31394159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_31394159
  · decide +kernel

theorem prime_2715845906941 : Nat.Prime 2715845906941 := by
  apply nodeValid_prime [2, 3, 5, 19, 29, 82148999] ⟨2715845906941, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (82148999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_82148999
  · decide +kernel

theorem prime_2718411037163 : Nat.Prime 2718411037163 := by
  apply nodeValid_prime [2, 239, 809, 7029731] ⟨2718411037163, 2, [(2, 1), (239, 1), (809, 1), (7029731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_809
    · exact prime_7029731
  · decide +kernel

theorem prime_2718411086213 : Nat.Prime 2718411086213 := by
  apply nodeValid_prime [2, 26321, 25819793] ⟨2718411086213, 2, [(2, 2), (26321, 1), (25819793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_26321
    · exact prime_25819793
  · decide +kernel

theorem prime_2718411086791 : Nat.Prime 2718411086791 := by
  apply nodeValid_prime [2, 3, 5, 7, 149, 1109, 26113] ⟨2718411086791, 11, [(2, 1), (3, 2), (5, 1), (7, 1), (149, 1), (1109, 1), (26113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_149
    · exact prime_1109
    · exact prime_26113
  · decide +kernel

theorem prime_2720977657621 : Nat.Prime 2720977657621 := by
  apply nodeValid_prime [2, 3, 5, 29, 1563780263] ⟨2720977657621, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (1563780263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1563780263
  · decide +kernel

theorem prime_2720977657763 : Nat.Prime 2720977657763 := by
  apply nodeValid_prime [2, 7, 13, 14950426691] ⟨2720977657763, 2, [(2, 1), (7, 1), (13, 1), (14950426691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_14950426691
  · decide +kernel

theorem prime_2720977841917 : Nat.Prime 2720977841917 := by
  apply nodeValid_prime [2, 3, 18131, 463189] ⟨2720977841917, 2, [(2, 2), (3, 4), (18131, 1), (463189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18131
    · exact prime_463189
  · decide +kernel

theorem prime_2723546243281 : Nat.Prime 2723546243281 := by
  apply nodeValid_prime [2, 3, 5, 19, 83, 7196011] ⟨2723546243281, 7, [(2, 4), (3, 1), (5, 1), (19, 1), (83, 1), (7196011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_83
    · exact prime_7196011
  · decide +kernel

theorem prime_2723546243459 : Nat.Prime 2723546243459 := by
  apply nodeValid_prime [2, 47, 827, 35034941] ⟨2723546243459, 2, [(2, 1), (47, 1), (827, 1), (35034941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_827
    · exact prime_35034941
  · decide +kernel

theorem prime_2723546287367 : Nat.Prime 2723546287367 := by
  apply nodeValid_prime [2, 37, 467, 78810877] ⟨2723546287367, 5, [(2, 1), (37, 1), (467, 1), (78810877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_467
    · exact prime_78810877
  · decide +kernel

theorem prime_2726116289021 : Nat.Prime 2726116289021 := by
  apply nodeValid_prime [2, 5, 397, 343339583] ⟨2726116289021, 2, [(2, 2), (5, 1), (397, 1), (343339583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_397
    · exact prime_343339583
  · decide +kernel

theorem prime_2726116289161 : Nat.Prime 2726116289161 := by
  apply nodeValid_prime [2, 3, 5, 11, 17477, 118169] ⟨2726116289161, 7, [(2, 3), (3, 1), (5, 1), (11, 1), (17477, 1), (118169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_17477
    · exact prime_118169
  · decide +kernel

theorem prime_2726116356637 : Nat.Prime 2726116356637 := by
  apply nodeValid_prime [2, 3, 19, 61, 109, 199807] ⟨2726116356637, 2, [(2, 2), (3, 3), (19, 1), (61, 1), (109, 1), (199807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_61
    · exact prime_109
    · exact prime_199807
  · decide +kernel

end Sude.Lucas.Generated
