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
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0081
import Sude.GeneratedFTT.N0100

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_7283 : Nat.Prime 7283 := by
  apply nodeValid_prime [2, 11, 331] ⟨7283, 2, [(2, 1), (11, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_331
  · decide +kernel

theorem prime_7411 : Nat.Prime 7411 := by
  apply nodeValid_prime [2, 3, 5, 13, 19] ⟨7411, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_8009 : Nat.Prime 8009 := by
  apply nodeValid_prime [2, 7, 11, 13] ⟨8009, 3, [(2, 3), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_12953 : Nat.Prime 12953 := by
  apply nodeValid_prime [2, 1619] ⟨12953, 3, [(2, 3), (1619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1619
  · decide +kernel

theorem prime_14537 : Nat.Prime 14537 := by
  apply nodeValid_prime [2, 23, 79] ⟨14537, 3, [(2, 3), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_14851 : Nat.Prime 14851 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨14851, 2, [(2, 1), (3, 3), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_22193 : Nat.Prime 22193 := by
  apply nodeValid_prime [2, 19, 73] ⟨22193, 3, [(2, 4), (19, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
  · decide +kernel

theorem prime_28447 : Nat.Prime 28447 := by
  apply nodeValid_prime [2, 3, 11, 431] ⟨28447, 3, [(2, 1), (3, 1), (11, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_431
  · decide +kernel

theorem prime_29989 : Nat.Prime 29989 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨29989, 2, [(2, 2), (3, 2), (7, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_38239 : Nat.Prime 38239 := by
  apply nodeValid_prime [2, 3, 6373] ⟨38239, 13, [(2, 1), (3, 1), (6373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6373
  · decide +kernel

theorem prime_40543 : Nat.Prime 40543 := by
  apply nodeValid_prime [2, 3, 29, 233] ⟨40543, 3, [(2, 1), (3, 1), (29, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_233
  · decide +kernel

theorem prime_42223 : Nat.Prime 42223 := by
  apply nodeValid_prime [2, 3, 31, 227] ⟨42223, 5, [(2, 1), (3, 1), (31, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_227
  · decide +kernel

theorem prime_42373 : Nat.Prime 42373 := by
  apply nodeValid_prime [2, 3, 11, 107] ⟨42373, 5, [(2, 2), (3, 2), (11, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_107
  · decide +kernel

theorem prime_47129 : Nat.Prime 47129 := by
  apply nodeValid_prime [2, 43, 137] ⟨47129, 3, [(2, 3), (43, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_137
  · decide +kernel

theorem prime_47303 : Nat.Prime 47303 := by
  apply nodeValid_prime [2, 67, 353] ⟨47303, 5, [(2, 1), (67, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_353
  · decide +kernel

theorem prime_55051 : Nat.Prime 55051 := by
  apply nodeValid_prime [2, 3, 5, 367] ⟨55051, 2, [(2, 1), (3, 1), (5, 2), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_367
  · decide +kernel

theorem prime_64187 : Nat.Prime 64187 := by
  apply nodeValid_prime [2, 67, 479] ⟨64187, 2, [(2, 1), (67, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_479
  · decide +kernel

theorem prime_82261 : Nat.Prime 82261 := by
  apply nodeValid_prime [2, 3, 5, 457] ⟨82261, 6, [(2, 2), (3, 2), (5, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_457
  · decide +kernel

theorem prime_86539 : Nat.Prime 86539 := by
  apply nodeValid_prime [2, 3, 14423] ⟨86539, 3, [(2, 1), (3, 1), (14423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_14423
  · decide +kernel

theorem prime_95561 : Nat.Prime 95561 := by
  apply nodeValid_prime [2, 5, 2389] ⟨95561, 3, [(2, 3), (5, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2389
  · decide +kernel

theorem prime_101159 : Nat.Prime 101159 := by
  apply nodeValid_prime [2, 37, 1367] ⟨101159, 7, [(2, 1), (37, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1367
  · decide +kernel

theorem prime_102251 : Nat.Prime 102251 := by
  apply nodeValid_prime [2, 5, 409] ⟨102251, 2, [(2, 1), (5, 3), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
  · decide +kernel

theorem prime_108529 : Nat.Prime 108529 := by
  apply nodeValid_prime [2, 3, 7, 17, 19] ⟨108529, 23, [(2, 4), (3, 1), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_112951 : Nat.Prime 112951 := by
  apply nodeValid_prime [2, 3, 5, 251] ⟨112951, 3, [(2, 1), (3, 2), (5, 2), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_251
  · decide +kernel

theorem prime_113963 : Nat.Prime 113963 := by
  apply nodeValid_prime [2, 19, 2999] ⟨113963, 2, [(2, 1), (19, 1), (2999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2999
  · decide +kernel

theorem prime_117041 : Nat.Prime 117041 := by
  apply nodeValid_prime [2, 5, 7, 11, 19] ⟨117041, 3, [(2, 4), (5, 1), (7, 1), (11, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_117071 : Nat.Prime 117071 := by
  apply nodeValid_prime [2, 5, 23, 509] ⟨117071, 11, [(2, 1), (5, 1), (23, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_509
  · decide +kernel

theorem prime_137869 : Nat.Prime 137869 := by
  apply nodeValid_prime [2, 3, 11489] ⟨137869, 11, [(2, 2), (3, 1), (11489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11489
  · decide +kernel

theorem prime_140611 : Nat.Prime 140611 := by
  apply nodeValid_prime [2, 3, 5, 43, 109] ⟨140611, 2, [(2, 1), (3, 1), (5, 1), (43, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_109
  · decide +kernel

theorem prime_141811 : Nat.Prime 141811 := by
  apply nodeValid_prime [2, 3, 5, 29, 163] ⟨141811, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_163
  · decide +kernel

theorem prime_168893 : Nat.Prime 168893 := by
  apply nodeValid_prime [2, 42223] ⟨168893, 2, [(2, 2), (42223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42223
  · decide +kernel

theorem prime_169957 : Nat.Prime 169957 := by
  apply nodeValid_prime [2, 3, 4721] ⟨169957, 2, [(2, 2), (3, 2), (4721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4721
  · decide +kernel

theorem prime_182111 : Nat.Prime 182111 := by
  apply nodeValid_prime [2, 5, 18211] ⟨182111, 13, [(2, 1), (5, 1), (18211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18211
  · decide +kernel

theorem prime_198689 : Nat.Prime 198689 := by
  apply nodeValid_prime [2, 7, 887] ⟨198689, 3, [(2, 5), (7, 1), (887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_887
  · decide +kernel

theorem prime_210709 : Nat.Prime 210709 := by
  apply nodeValid_prime [2, 3, 1951] ⟨210709, 2, [(2, 2), (3, 3), (1951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1951
  · decide +kernel

theorem prime_214771 : Nat.Prime 214771 := by
  apply nodeValid_prime [2, 3, 5, 7159] ⟨214771, 2, [(2, 1), (3, 1), (5, 1), (7159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7159
  · decide +kernel

theorem prime_226937 : Nat.Prime 226937 := by
  apply nodeValid_prime [2, 19, 1493] ⟨226937, 3, [(2, 3), (19, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_1493
  · decide +kernel

theorem prime_227489 : Nat.Prime 227489 := by
  apply nodeValid_prime [2, 7109] ⟨227489, 3, [(2, 5), (7109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7109
  · decide +kernel

theorem prime_295819 : Nat.Prime 295819 := by
  apply nodeValid_prime [2, 3, 47, 1049] ⟨295819, 2, [(2, 1), (3, 1), (47, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_1049
  · decide +kernel

theorem prime_301177 : Nat.Prime 301177 := by
  apply nodeValid_prime [2, 3, 47, 89] ⟨301177, 5, [(2, 3), (3, 2), (47, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_89
  · decide +kernel

theorem prime_365567 : Nat.Prime 365567 := by
  apply nodeValid_prime [2, 47, 3889] ⟨365567, 5, [(2, 1), (47, 1), (3889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_3889
  · decide +kernel

theorem prime_385141 : Nat.Prime 385141 := by
  apply nodeValid_prime [2, 3, 5, 7, 131] ⟨385141, 2, [(2, 2), (3, 1), (5, 1), (7, 2), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_131
  · decide +kernel

theorem prime_389971 : Nat.Prime 389971 := by
  apply nodeValid_prime [2, 3, 5, 7, 619] ⟨389971, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_619
  · decide +kernel

theorem prime_436831 : Nat.Prime 436831 := by
  apply nodeValid_prime [2, 3, 5, 14561] ⟨436831, 6, [(2, 1), (3, 1), (5, 1), (14561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_14561
  · decide +kernel

theorem prime_495361 : Nat.Prime 495361 := by
  apply nodeValid_prime [2, 3, 5, 43] ⟨495361, 14, [(2, 8), (3, 2), (5, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
  · decide +kernel

theorem prime_520717 : Nat.Prime 520717 := by
  apply nodeValid_prime [2, 3, 7, 6199] ⟨520717, 2, [(2, 2), (3, 1), (7, 1), (6199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6199
  · decide +kernel

theorem prime_532633 : Nat.Prime 532633 := by
  apply nodeValid_prime [2, 3, 22193] ⟨532633, 5, [(2, 3), (3, 1), (22193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22193
  · decide +kernel

theorem prime_563501 : Nat.Prime 563501 := by
  apply nodeValid_prime [2, 5, 7, 23] ⟨563501, 2, [(2, 2), (5, 3), (7, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_575551 : Nat.Prime 575551 := by
  apply nodeValid_prime [2, 3, 5, 1279] ⟨575551, 6, [(2, 1), (3, 2), (5, 2), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1279
  · decide +kernel

theorem prime_613507 : Nat.Prime 613507 := by
  apply nodeValid_prime [2, 3, 102251] ⟨613507, 2, [(2, 1), (3, 1), (102251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102251
  · decide +kernel

theorem prime_702809 : Nat.Prime 702809 := by
  apply nodeValid_prime [2, 59, 1489] ⟨702809, 3, [(2, 3), (59, 1), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_1489
  · decide +kernel

theorem prime_768457 : Nat.Prime 768457 := by
  apply nodeValid_prime [2, 3, 13, 821] ⟨768457, 5, [(2, 3), (3, 2), (13, 1), (821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_821
  · decide +kernel

theorem prime_822611 : Nat.Prime 822611 := by
  apply nodeValid_prime [2, 5, 82261] ⟨822611, 2, [(2, 1), (5, 1), (82261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_82261
  · decide +kernel

theorem prime_828871 : Nat.Prime 828871 := by
  apply nodeValid_prime [2, 3, 5, 7, 3947] ⟨828871, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (3947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_3947
  · decide +kernel

theorem prime_866783 : Nat.Prime 866783 := by
  apply nodeValid_prime [2, 7, 101, 613] ⟨866783, 5, [(2, 1), (7, 1), (101, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_101
    · exact prime_613
  · decide +kernel

theorem prime_882313 : Nat.Prime 882313 := by
  apply nodeValid_prime [2, 3, 97, 379] ⟨882313, 5, [(2, 3), (3, 1), (97, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_379
  · decide +kernel

theorem prime_1108819 : Nat.Prime 1108819 := by
  apply nodeValid_prime [2, 3, 229, 269] ⟨1108819, 2, [(2, 1), (3, 2), (229, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
    · exact prime_269
  · decide +kernel

theorem prime_1152037 : Nat.Prime 1152037 := by
  apply nodeValid_prime [2, 3, 10667] ⟨1152037, 2, [(2, 2), (3, 3), (10667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10667
  · decide +kernel

theorem prime_1183277 : Nat.Prime 1183277 := by
  apply nodeValid_prime [2, 295819] ⟨1183277, 2, [(2, 2), (295819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_295819
  · decide +kernel

theorem prime_1209973 : Nat.Prime 1209973 := by
  apply nodeValid_prime [2, 3, 59, 1709] ⟨1209973, 2, [(2, 2), (3, 1), (59, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_1709
  · decide +kernel

theorem prime_1377653 : Nat.Prime 1377653 := by
  apply nodeValid_prime [2, 19, 18127] ⟨1377653, 2, [(2, 2), (19, 1), (18127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_18127
  · decide +kernel

theorem prime_1377931 : Nat.Prime 1377931 := by
  apply nodeValid_prime [2, 3, 5, 23, 1997] ⟨1377931, 2, [(2, 1), (3, 1), (5, 1), (23, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_1997
  · decide +kernel

theorem prime_1573021 : Nat.Prime 1573021 := by
  apply nodeValid_prime [2, 3, 5, 971] ⟨1573021, 6, [(2, 2), (3, 4), (5, 1), (971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_971
  · decide +kernel

theorem prime_1589513 : Nat.Prime 1589513 := by
  apply nodeValid_prime [2, 198689] ⟨1589513, 3, [(2, 3), (198689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_198689
  · decide +kernel

theorem prime_1663793 : Nat.Prime 1663793 := by
  apply nodeValid_prime [2, 13, 19, 421] ⟨1663793, 3, [(2, 4), (13, 1), (19, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_421
  · decide +kernel

theorem prime_1715059 : Nat.Prime 1715059 := by
  apply nodeValid_prime [2, 3, 151, 631] ⟨1715059, 2, [(2, 1), (3, 2), (151, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_631
  · decide +kernel

theorem prime_1810607 : Nat.Prime 1810607 := by
  apply nodeValid_prime [2, 7, 23, 5623] ⟨1810607, 5, [(2, 1), (7, 1), (23, 1), (5623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_5623
  · decide +kernel

theorem prime_1847929 : Nat.Prime 1847929 := by
  apply nodeValid_prime [2, 3, 37, 2081] ⟨1847929, 11, [(2, 3), (3, 1), (37, 1), (2081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_2081
  · decide +kernel

theorem prime_1986869 : Nat.Prime 1986869 := by
  apply nodeValid_prime [2, 13, 19, 2011] ⟨1986869, 2, [(2, 2), (13, 1), (19, 1), (2011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_2011
  · decide +kernel

theorem prime_2545313 : Nat.Prime 2545313 := by
  apply nodeValid_prime [2, 7, 11, 1033] ⟨2545313, 3, [(2, 5), (7, 1), (11, 1), (1033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_1033
  · decide +kernel

theorem prime_2666969 : Nat.Prime 2666969 := by
  apply nodeValid_prime [2, 41, 47, 173] ⟨2666969, 3, [(2, 3), (41, 1), (47, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_47
    · exact prime_173
  · decide +kernel

theorem prime_2755307 : Nat.Prime 2755307 := by
  apply nodeValid_prime [2, 1377653] ⟨2755307, 2, [(2, 1), (1377653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1377653
  · decide +kernel

theorem prime_2819521 : Nat.Prime 2819521 := by
  apply nodeValid_prime [2, 3, 5, 11, 89] ⟨2819521, 7, [(2, 6), (3, 2), (5, 1), (11, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_89
  · decide +kernel

theorem prime_2921929 : Nat.Prime 2921929 := by
  apply nodeValid_prime [2, 3, 211, 577] ⟨2921929, 7, [(2, 3), (3, 1), (211, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_577
  · decide +kernel

theorem prime_3179027 : Nat.Prime 3179027 := by
  apply nodeValid_prime [2, 1589513] ⟨3179027, 2, [(2, 1), (1589513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1589513
  · decide +kernel

theorem prime_4786447 : Nat.Prime 4786447 := by
  apply nodeValid_prime [2, 3, 7, 113963] ⟨4786447, 3, [(2, 1), (3, 1), (7, 1), (113963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113963
  · decide +kernel

theorem prime_5624441 : Nat.Prime 5624441 := by
  apply nodeValid_prime [2, 5, 140611] ⟨5624441, 3, [(2, 3), (5, 1), (140611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_140611
  · decide +kernel

theorem prime_6080149 : Nat.Prime 6080149 := by
  apply nodeValid_prime [2, 3, 168893] ⟨6080149, 6, [(2, 2), (3, 2), (168893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_168893
  · decide +kernel

theorem prime_6421111 : Nat.Prime 6421111 := by
  apply nodeValid_prime [2, 3, 5, 193, 1109] ⟨6421111, 3, [(2, 1), (3, 1), (5, 1), (193, 1), (1109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_193
    · exact prime_1109
  · decide +kernel

theorem prime_7259839 : Nat.Prime 7259839 := by
  apply nodeValid_prime [2, 3, 1209973] ⟨7259839, 6, [(2, 1), (3, 1), (1209973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1209973
  · decide +kernel

theorem prime_8404189 : Nat.Prime 8404189 := by
  apply nodeValid_prime [2, 3, 13, 17, 3169] ⟨8404189, 6, [(2, 2), (3, 1), (13, 1), (17, 1), (3169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_3169
  · decide +kernel

theorem prime_13370761 : Nat.Prime 13370761 := by
  apply nodeValid_prime [2, 3, 5, 13, 2857] ⟨13370761, 14, [(2, 3), (3, 2), (5, 1), (13, 1), (2857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_2857
  · decide +kernel

theorem prime_14806999 : Nat.Prime 14806999 := by
  apply nodeValid_prime [2, 3, 822611] ⟨14806999, 3, [(2, 1), (3, 2), (822611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_822611
  · decide +kernel

theorem prime_14907517 : Nat.Prime 14907517 := by
  apply nodeValid_prime [2, 3, 13, 95561] ⟨14907517, 2, [(2, 2), (3, 1), (13, 1), (95561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_95561
  · decide +kernel

theorem prime_17060699 : Nat.Prime 17060699 := by
  apply nodeValid_prime [2, 181, 47129] ⟨17060699, 2, [(2, 1), (181, 1), (47129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_47129
  · decide +kernel

theorem prime_17233991 : Nat.Prime 17233991 := by
  apply nodeValid_prime [2, 5, 97, 109, 163] ⟨17233991, 11, [(2, 1), (5, 1), (97, 1), (109, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
    · exact prime_109
    · exact prime_163
  · decide +kernel

theorem prime_18479291 : Nat.Prime 18479291 := by
  apply nodeValid_prime [2, 5, 1847929] ⟨18479291, 2, [(2, 1), (5, 1), (1847929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1847929
  · decide +kernel

theorem prime_25419307 : Nat.Prime 25419307 := by
  apply nodeValid_prime [2, 3, 11, 385141] ⟨25419307, 2, [(2, 1), (3, 1), (11, 1), (385141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_385141
  · decide +kernel

theorem prime_31977623 : Nat.Prime 31977623 := by
  apply nodeValid_prime [2, 41, 389971] ⟨31977623, 5, [(2, 1), (41, 1), (389971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_389971
  · decide +kernel

theorem prime_32174227 : Nat.Prime 32174227 := by
  apply nodeValid_prime [2, 3, 7, 47, 1811] ⟨32174227, 2, [(2, 1), (3, 3), (7, 1), (47, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_1811
  · decide +kernel

theorem prime_43574159 : Nat.Prime 43574159 := by
  apply nodeValid_prime [2, 31, 702809] ⟨43574159, 13, [(2, 1), (31, 1), (702809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_702809
  · decide +kernel

theorem prime_45112337 : Nat.Prime 45112337 := by
  apply nodeValid_prime [2, 2819521] ⟨45112337, 3, [(2, 4), (2819521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2819521
  · decide +kernel

theorem prime_77763139 : Nat.Prime 77763139 := by
  apply nodeValid_prime [2, 3, 23, 563501] ⟨77763139, 2, [(2, 1), (3, 1), (23, 1), (563501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_563501
  · decide +kernel

theorem prime_90923159 : Nat.Prime 90923159 := by
  apply nodeValid_prime [2, 41, 1108819] ⟨90923159, 13, [(2, 1), (41, 1), (1108819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1108819
  · decide +kernel

theorem prime_100165129 : Nat.Prime 100165129 := by
  apply nodeValid_prime [2, 3, 7, 263, 2267] ⟨100165129, 17, [(2, 3), (3, 1), (7, 1), (263, 1), (2267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_263
    · exact prime_2267
  · decide +kernel

theorem prime_101239939 : Nat.Prime 101239939 := by
  apply nodeValid_prime [2, 3, 5624441] ⟨101239939, 10, [(2, 1), (3, 2), (5624441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5624441
  · decide +kernel

theorem prime_111700499 : Nat.Prime 111700499 := by
  apply nodeValid_prime [2, 7, 13, 43, 2039] ⟨111700499, 2, [(2, 1), (7, 2), (13, 1), (43, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_2039
  · decide +kernel

theorem prime_143086199 : Nat.Prime 143086199 := by
  apply nodeValid_prime [2, 43, 1663793] ⟨143086199, 7, [(2, 1), (43, 1), (1663793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1663793
  · decide +kernel

theorem prime_151275403 : Nat.Prime 151275403 := by
  apply nodeValid_prime [2, 3, 8404189] ⟨151275403, 2, [(2, 1), (3, 2), (8404189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8404189
  · decide +kernel

theorem prime_271776649 : Nat.Prime 271776649 := by
  apply nodeValid_prime [2, 3, 11, 13, 23, 313] ⟨271776649, 19, [(2, 3), (3, 1), (11, 2), (13, 1), (23, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_313
  · decide +kernel

theorem prime_278161661 : Nat.Prime 278161661 := by
  apply nodeValid_prime [2, 5, 7, 1986869] ⟨278161661, 2, [(2, 2), (5, 1), (7, 1), (1986869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_1986869
  · decide +kernel

theorem prime_321742271 : Nat.Prime 321742271 := by
  apply nodeValid_prime [2, 5, 32174227] ⟨321742271, 11, [(2, 1), (5, 1), (32174227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_32174227
  · decide +kernel

theorem prime_349705927 : Nat.Prime 349705927 := by
  apply nodeValid_prime [2, 3, 137, 141811] ⟨349705927, 5, [(2, 1), (3, 2), (137, 1), (141811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_141811
  · decide +kernel

theorem prime_414396721 : Nat.Prime 414396721 := by
  apply nodeValid_prime [2, 3, 5, 575551] ⟨414396721, 17, [(2, 4), (3, 2), (5, 1), (575551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_575551
  · decide +kernel

theorem prime_455250493 : Nat.Prime 455250493 := by
  apply nodeValid_prime [2, 3, 1217, 10391] ⟨455250493, 5, [(2, 2), (3, 2), (1217, 1), (10391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1217
    · exact prime_10391
  · decide +kernel

theorem prime_708401891 : Nat.Prime 708401891 := by
  apply nodeValid_prime [2, 5, 7, 19, 532633] ⟨708401891, 2, [(2, 1), (5, 1), (7, 1), (19, 1), (532633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_532633
  · decide +kernel

theorem prime_898230083 : Nat.Prime 898230083 := by
  apply nodeValid_prime [2, 163, 2755307] ⟨898230083, 2, [(2, 1), (163, 1), (2755307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_2755307
  · decide +kernel

theorem prime_926955383 : Nat.Prime 926955383 := by
  apply nodeValid_prime [2, 1061, 436831] ⟨926955383, 5, [(2, 1), (1061, 1), (436831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1061
    · exact prime_436831
  · decide +kernel

theorem prime_1186598111 : Nat.Prime 1186598111 := by
  apply nodeValid_prime [2, 5, 103, 1152037] ⟨1186598111, 37, [(2, 1), (5, 1), (103, 1), (1152037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_1152037
  · decide +kernel

theorem prime_1274171011 : Nat.Prime 1274171011 := by
  apply nodeValid_prime [2, 3, 5, 7, 866783] ⟨1274171011, 2, [(2, 1), (3, 1), (5, 1), (7, 2), (866783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_866783
  · decide +kernel

theorem prime_1323635101 : Nat.Prime 1323635101 := by
  apply nodeValid_prime [2, 3, 5, 571, 7727] ⟨1323635101, 6, [(2, 2), (3, 1), (5, 2), (571, 1), (7727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_571
    · exact prime_7727
  · decide +kernel

theorem prime_1378719281 : Nat.Prime 1378719281 := by
  apply nodeValid_prime [2, 5, 17233991] ⟨1378719281, 3, [(2, 4), (5, 1), (17233991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17233991
  · decide +kernel

theorem prime_2864324707 : Nat.Prime 2864324707 := by
  apply nodeValid_prime [2, 3, 179, 2666969] ⟨2864324707, 2, [(2, 1), (3, 1), (179, 1), (2666969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_2666969
  · decide +kernel

theorem prime_2877869003 : Nat.Prime 2877869003 := by
  apply nodeValid_prime [2, 839, 1715059] ⟨2877869003, 2, [(2, 1), (839, 1), (1715059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_839
    · exact prime_1715059
  · decide +kernel

theorem prime_4884747191 : Nat.Prime 4884747191 := by
  apply nodeValid_prime [2, 5, 17, 31, 103, 8999] ⟨4884747191, 7, [(2, 1), (5, 1), (17, 1), (31, 1), (103, 1), (8999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_31
    · exact prime_103
    · exact prime_8999
  · decide +kernel

theorem prime_5595294833 : Nat.Prime 5595294833 := by
  apply nodeValid_prime [2, 349705927] ⟨5595294833, 3, [(2, 4), (349705927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_349705927
  · decide +kernel

theorem prime_5617461041 : Nat.Prime 5617461041 := by
  apply nodeValid_prime [2, 5, 647, 108529] ⟨5617461041, 3, [(2, 4), (5, 1), (647, 1), (108529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_647
    · exact prime_108529
  · decide +kernel

theorem prime_8031341701 : Nat.Prime 8031341701 := by
  apply nodeValid_prime [2, 3, 5, 1117, 2663] ⟨8031341701, 6, [(2, 2), (3, 3), (5, 2), (1117, 1), (2663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1117
    · exact prime_2663
  · decide +kernel

theorem prime_8153299471 : Nat.Prime 8153299471 := by
  apply nodeValid_prime [2, 3, 5, 271776649] ⟨8153299471, 13, [(2, 1), (3, 1), (5, 1), (271776649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_271776649
  · decide +kernel

theorem prime_11029754249 : Nat.Prime 11029754249 := by
  apply nodeValid_prime [2, 1378719281] ⟨11029754249, 3, [(2, 3), (1378719281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1378719281
  · decide +kernel

theorem prime_13701873701 : Nat.Prime 13701873701 := by
  apply nodeValid_prime [2, 5, 73, 103, 18223] ⟨13701873701, 2, [(2, 2), (5, 2), (73, 1), (103, 1), (18223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_73
    · exact prime_103
    · exact prime_18223
  · decide +kernel

theorem prime_16205861741 : Nat.Prime 16205861741 := by
  apply nodeValid_prime [2, 5, 18043, 44909] ⟨16205861741, 2, [(2, 2), (5, 1), (18043, 1), (44909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18043
    · exact prime_44909
  · decide +kernel

theorem prime_45152403677 : Nat.Prime 45152403677 := by
  apply nodeValid_prime [2, 353, 31977623] ⟨45152403677, 2, [(2, 2), (353, 1), (31977623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_353
    · exact prime_31977623
  · decide +kernel

theorem prime_45957307873 : Nat.Prime 45957307873 := by
  apply nodeValid_prime [2, 3, 7, 8009, 8539] ⟨45957307873, 5, [(2, 5), (3, 1), (7, 1), (8009, 1), (8539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8009
    · exact prime_8539
  · decide +kernel

theorem prime_52945404041 : Nat.Prime 52945404041 := by
  apply nodeValid_prime [2, 5, 1323635101] ⟨52945404041, 3, [(2, 3), (5, 1), (1323635101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1323635101
  · decide +kernel

theorem prime_82649894389 : Nat.Prime 82649894389 := by
  apply nodeValid_prime [2, 3, 32069, 214771] ⟨82649894389, 2, [(2, 2), (3, 1), (32069, 1), (214771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32069
    · exact prime_214771
  · decide +kernel

theorem prime_97235170447 : Nat.Prime 97235170447 := by
  apply nodeValid_prime [2, 3, 16205861741] ⟨97235170447, 5, [(2, 1), (3, 1), (16205861741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16205861741
  · decide +kernel

theorem prime_110982966673 : Nat.Prime 110982966673 := by
  apply nodeValid_prime [2, 3, 1277, 1810607] ⟨110982966673, 15, [(2, 4), (3, 1), (1277, 1), (1810607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1277
    · exact prime_1810607
  · decide +kernel

theorem prime_205345718953 : Nat.Prime 205345718953 := by
  apply nodeValid_prime [2, 3, 11, 37, 701, 29989] ⟨205345718953, 10, [(2, 3), (3, 1), (11, 1), (37, 1), (701, 1), (29989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_701
    · exact prime_29989
  · decide +kernel

theorem prime_235933363727 : Nat.Prime 235933363727 := by
  apply nodeValid_prime [2, 37, 41, 77763139] ⟨235933363727, 5, [(2, 1), (37, 1), (41, 1), (77763139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_41
    · exact prime_77763139
  · decide +kernel

theorem prime_827964648559 : Nat.Prime 827964648559 := by
  apply nodeValid_prime [2, 3, 37, 414396721] ⟨827964648559, 6, [(2, 1), (3, 3), (37, 1), (414396721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_414396721
  · decide +kernel

theorem prime_831636546043 : Nat.Prime 831636546043 := by
  apply nodeValid_prime [2, 3, 17, 8153299471] ⟨831636546043, 2, [(2, 1), (3, 1), (17, 1), (8153299471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8153299471
  · decide +kernel

theorem prime_1650070021991 : Nat.Prime 1650070021991 := by
  apply nodeValid_prime [2, 5, 13, 17, 1217, 613507] ⟨1650070021991, 23, [(2, 1), (5, 1), (13, 1), (17, 1), (1217, 1), (613507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_1217
    · exact prime_613507
  · decide +kernel

theorem prime_1654463083139 : Nat.Prime 1654463083139 := by
  apply nodeValid_prime [2, 8171, 101239939] ⟨1654463083139, 2, [(2, 1), (8171, 1), (101239939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8171
    · exact prime_101239939
  · decide +kernel

theorem prime_3276787414009 : Nat.Prime 3276787414009 := by
  apply nodeValid_prime [2, 3, 17, 8031341701] ⟨3276787414009, 19, [(2, 3), (3, 1), (17, 1), (8031341701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_8031341701
  · decide +kernel

theorem prime_3276787464809 : Nat.Prime 3276787464809 := by
  apply nodeValid_prime [2, 11, 13, 2864324707] ⟨3276787464809, 3, [(2, 3), (11, 1), (13, 1), (2864324707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_2864324707
  · decide +kernel

theorem prime_3276787465697 : Nat.Prime 3276787465697 := by
  apply nodeValid_prime [2, 86539, 1183277] ⟨3276787465697, 3, [(2, 5), (86539, 1), (1183277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_86539
    · exact prime_1183277
  · decide +kernel

theorem prime_3279700355707 : Nat.Prime 3279700355707 := by
  apply nodeValid_prime [2, 3, 29, 7121, 882313] ⟨3279700355707, 2, [(2, 1), (3, 2), (29, 1), (7121, 1), (882313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_7121
    · exact prime_882313
  · decide +kernel

theorem prime_3279700356089 : Nat.Prime 3279700356089 := by
  apply nodeValid_prime [2, 13, 23, 61, 199, 112951] ⟨3279700356089, 3, [(2, 3), (13, 1), (23, 1), (61, 1), (199, 1), (112951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_61
    · exact prime_199
    · exact prime_112951
  · decide +kernel

theorem prime_3279700360351 : Nat.Prime 3279700360351 := by
  apply nodeValid_prime [2, 3, 5, 239, 2749, 11093] ⟨3279700360351, 6, [(2, 1), (3, 2), (5, 2), (239, 1), (2749, 1), (11093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_239
    · exact prime_2749
    · exact prime_11093
  · decide +kernel

theorem prime_3282614972177 : Nat.Prime 3282614972177 := by
  apply nodeValid_prime [2, 199, 223, 383, 12071] ⟨3282614972177, 3, [(2, 4), (199, 1), (223, 1), (383, 1), (12071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_223
    · exact prime_383
    · exact prime_12071
  · decide +kernel

theorem prime_3282614973193 : Nat.Prime 3282614973193 := by
  apply nodeValid_prime [2, 3, 8017, 17060699] ⟨3282614973193, 5, [(2, 3), (3, 1), (8017, 1), (17060699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8017
    · exact prime_17060699
  · decide +kernel

theorem prime_3282615050543 : Nat.Prime 3282615050543 := by
  apply nodeValid_prime [2, 31, 52945404041] ⟨3282615050543, 5, [(2, 1), (31, 1), (52945404041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_52945404041
  · decide +kernel

theorem prime_3285531495497 : Nat.Prime 3285531495497 := by
  apply nodeValid_prime [2, 263, 7411, 210709] ⟨3285531495497, 3, [(2, 3), (263, 1), (7411, 1), (210709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_7411
    · exact prime_210709
  · decide +kernel

theorem prime_3285531503249 : Nat.Prime 3285531503249 := by
  apply nodeValid_prime [2, 205345718953] ⟨3285531503249, 3, [(2, 4), (205345718953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_205345718953
  · decide +kernel

theorem prime_3285531503711 : Nat.Prime 3285531503711 := by
  apply nodeValid_prime [2, 5, 7283, 45112337] ⟨3285531503711, 7, [(2, 1), (5, 1), (7283, 1), (45112337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7283
    · exact prime_45112337
  · decide +kernel

theorem prime_3288449688241 : Nat.Prime 3288449688241 := by
  apply nodeValid_prime [2, 3, 5, 13701873701] ⟨3288449688241, 17, [(2, 4), (3, 1), (5, 1), (13701873701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13701873701
  · decide +kernel

theorem prime_3288449702779 : Nat.Prime 3288449702779 := by
  apply nodeValid_prime [2, 3, 37, 28447, 520717] ⟨3288449702779, 2, [(2, 1), (3, 1), (37, 1), (28447, 1), (520717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_28447
    · exact prime_520717
  · decide +kernel

theorem prime_3288449703397 : Nat.Prime 3288449703397 := by
  apply nodeValid_prime [2, 3, 11, 13, 4297, 40543] ⟨3288449703397, 2, [(2, 2), (3, 1), (11, 2), (13, 1), (4297, 1), (40543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_4297
    · exact prime_40543
  · decide +kernel

theorem prime_3291369639539 : Nat.Prime 3291369639539 := by
  apply nodeValid_prime [2, 23, 401, 4211, 42373] ⟨3291369639539, 2, [(2, 1), (23, 1), (401, 1), (4211, 1), (42373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_401
    · exact prime_4211
    · exact prime_42373
  · decide +kernel

theorem prime_3291369693347 : Nat.Prime 3291369693347 := by
  apply nodeValid_prime [2, 7, 37, 101, 127, 495361] ⟨3291369693347, 2, [(2, 1), (7, 1), (37, 1), (101, 1), (127, 1), (495361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_101
    · exact prime_127
    · exact prime_495361
  · decide +kernel

theorem prime_3291369693431 : Nat.Prime 3291369693431 := by
  apply nodeValid_prime [2, 5, 7, 13, 29, 2545313] ⟨3291369693431, 7, [(2, 1), (5, 1), (7, 3), (13, 1), (29, 1), (2545313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_2545313
  · decide +kernel

theorem prime_3294291293539 : Nat.Prime 3294291293539 := by
  apply nodeValid_prime [2, 3, 7, 2341, 4786447] ⟨3294291293539, 12, [(2, 1), (3, 1), (7, 2), (2341, 1), (4786447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2341
    · exact prime_4786447
  · decide +kernel

theorem prime_3294291294113 : Nat.Prime 3294291294113 := by
  apply nodeValid_prime [2, 7, 13, 821, 1377931] ⟨3294291294113, 3, [(2, 5), (7, 1), (13, 1), (821, 1), (1377931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_821
    · exact prime_1377931
  · decide +kernel

theorem prime_3294291348587 : Nat.Prime 3294291348587 := by
  apply nodeValid_prime [2, 7, 9257, 25419307] ⟨3294291348587, 2, [(2, 1), (7, 1), (9257, 1), (25419307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9257
    · exact prime_25419307
  · decide +kernel

theorem prime_3297214793209 : Nat.Prime 3297214793209 := by
  apply nodeValid_prime [2, 3, 7, 61, 321742271] ⟨3297214793209, 11, [(2, 3), (3, 1), (7, 1), (61, 1), (321742271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_61
    · exact prime_321742271
  · decide +kernel

theorem prime_3297214795027 : Nat.Prime 3297214795027 := by
  apply nodeValid_prime [2, 3, 191, 193, 14907517] ⟨3297214795027, 3, [(2, 1), (3, 1), (191, 1), (193, 1), (14907517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_193
    · exact prime_14907517
  · decide +kernel

theorem prime_3297214814057 : Nat.Prime 3297214814057 := by
  apply nodeValid_prime [2, 64187, 6421111] ⟨3297214814057, 3, [(2, 3), (64187, 1), (6421111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_64187
    · exact prime_6421111
  · decide +kernel

theorem prime_3300140043983 : Nat.Prime 3300140043983 := by
  apply nodeValid_prime [2, 1650070021991] ⟨3300140043983, 5, [(2, 1), (1650070021991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1650070021991
  · decide +kernel

theorem prime_3300140093737 : Nat.Prime 3300140093737 := by
  apply nodeValid_prime [2, 3, 31, 143086199] ⟨3300140093737, 15, [(2, 3), (3, 1), (31, 2), (143086199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_143086199
  · decide +kernel

theorem prime_3300140093827 : Nat.Prime 3300140093827 := by
  apply nodeValid_prime [2, 3, 83, 29201, 226937] ⟨3300140093827, 2, [(2, 1), (3, 1), (83, 1), (29201, 1), (226937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_29201
    · exact prime_226937
  · decide +kernel

theorem prime_3303067028543 : Nat.Prime 3303067028543 := by
  apply nodeValid_prime [2, 227489, 7259839] ⟨3303067028543, 5, [(2, 1), (227489, 1), (7259839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227489
    · exact prime_7259839
  · decide +kernel

theorem prime_3303067092109 : Nat.Prime 3303067092109 := by
  apply nodeValid_prime [2, 3, 7, 5617461041] ⟨3303067092109, 2, [(2, 2), (3, 1), (7, 2), (5617461041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5617461041
  · decide +kernel

theorem prime_3303067092179 : Nat.Prime 3303067092179 := by
  apply nodeValid_prime [2, 7, 235933363727] ⟨3303067092179, 2, [(2, 1), (7, 1), (235933363727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_235933363727
  · decide +kernel

theorem prime_3305995775561 : Nat.Prime 3305995775561 := by
  apply nodeValid_prime [2, 5, 82649894389] ⟨3305995775561, 3, [(2, 3), (5, 1), (82649894389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_82649894389
  · decide +kernel

theorem prime_3305995794091 : Nat.Prime 3305995794091 := by
  apply nodeValid_prime [2, 3, 5, 11, 491, 68699] ⟨3305995794091, 3, [(2, 1), (3, 4), (5, 1), (11, 2), (491, 1), (68699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_491
    · exact prime_68699
  · decide +kernel

theorem prime_3305995795199 : Nat.Prime 3305995795199 := by
  apply nodeValid_prime [2, 17, 97235170447] ⟨3305995795199, 11, [(2, 1), (17, 1), (97235170447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_97235170447
  · decide +kernel

theorem prime_3308926166279 : Nat.Prime 3308926166279 := by
  apply nodeValid_prime [2, 1654463083139] ⟨3308926166279, 13, [(2, 1), (1654463083139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1654463083139
  · decide +kernel

theorem prime_3308926166857 : Nat.Prime 3308926166857 := by
  apply nodeValid_prime [2, 3, 45957307873] ⟨3308926166857, 5, [(2, 3), (3, 2), (45957307873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_45957307873
  · decide +kernel

theorem prime_3308926274701 : Nat.Prime 3308926274701 := by
  apply nodeValid_prime [2, 3, 5, 11029754249] ⟨3308926274701, 2, [(2, 2), (3, 1), (5, 2), (11029754249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11029754249
  · decide +kernel

theorem prime_3311858533021 : Nat.Prime 3311858533021 := by
  apply nodeValid_prime [2, 3, 5, 29, 103, 18479291] ⟨3311858533021, 6, [(2, 2), (3, 1), (5, 1), (29, 1), (103, 1), (18479291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_103
    · exact prime_18479291
  · decide +kernel

theorem prime_3311858594237 : Nat.Prime 3311858594237 := by
  apply nodeValid_prime [2, 827964648559] ⟨3311858594237, 2, [(2, 2), (827964648559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_827964648559
  · decide +kernel

theorem prime_3311858595499 : Nat.Prime 3311858595499 := by
  apply nodeValid_prime [2, 3, 113, 4884747191] ⟨3311858595499, 2, [(2, 1), (3, 1), (113, 1), (4884747191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_4884747191
  · decide +kernel

theorem prime_3314792448727 : Nat.Prime 3314792448727 := by
  apply nodeValid_prime [2, 3, 11, 43, 283, 409, 10091] ⟨3314792448727, 3, [(2, 1), (3, 1), (11, 1), (43, 1), (283, 1), (409, 1), (10091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_283
    · exact prime_409
    · exact prime_10091
  · decide +kernel

theorem prime_3314792449609 : Nat.Prime 3314792449609 := by
  apply nodeValid_prime [2, 3, 149, 926955383] ⟨3314792449609, 41, [(2, 3), (3, 1), (149, 1), (926955383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_926955383
  · decide +kernel

theorem prime_3314792546839 : Nat.Prime 3314792546839 := by
  apply nodeValid_prime [2, 3, 117071, 1573021] ⟨3314792546839, 3, [(2, 1), (3, 2), (117071, 1), (1573021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_117071
    · exact prime_1573021
  · decide +kernel

theorem prime_3317728221299 : Nat.Prime 3317728221299 := by
  apply nodeValid_prime [2, 14851, 111700499] ⟨3317728221299, 2, [(2, 1), (14851, 1), (111700499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_14851
    · exact prime_111700499
  · decide +kernel

theorem prime_3317728221439 : Nat.Prime 3317728221439 := by
  apply nodeValid_prime [2, 3, 17, 23, 43, 281, 117041] ⟨3317728221439, 3, [(2, 1), (3, 1), (17, 1), (23, 1), (43, 1), (281, 1), (117041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_43
    · exact prime_281
    · exact prime_117041
  · decide +kernel

theorem prime_3317728318357 : Nat.Prime 3317728318357 := by
  apply nodeValid_prime [2, 3, 233, 1186598111] ⟨3317728318357, 5, [(2, 2), (3, 1), (233, 1), (1186598111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
    · exact prime_1186598111
  · decide +kernel

theorem prime_3320665844929 : Nat.Prime 3320665844929 := by
  apply nodeValid_prime [2, 3, 1787, 1823, 5309] ⟨3320665844929, 7, [(2, 6), (3, 1), (1787, 1), (1823, 1), (5309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1787
    · exact prime_1823
    · exact prime_5309
  · decide +kernel

theorem prime_3320665858541 : Nat.Prime 3320665858541 := by
  apply nodeValid_prime [2, 5, 29, 131, 317, 137869] ⟨3320665858541, 3, [(2, 2), (5, 1), (29, 1), (131, 1), (317, 1), (137869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_131
    · exact prime_317
    · exact prime_137869
  · decide +kernel

theorem prime_3323605130803 : Nat.Prime 3323605130803 := by
  apply nodeValid_prime [2, 3, 11, 5595294833] ⟨3323605130803, 5, [(2, 1), (3, 3), (11, 1), (5595294833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_5595294833
  · decide +kernel

theorem prime_3323605154087 : Nat.Prime 3323605154087 := by
  apply nodeValid_prime [2, 7, 373, 90923159] ⟨3323605154087, 5, [(2, 1), (7, 2), (373, 1), (90923159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_373
    · exact prime_90923159
  · decide +kernel

theorem prime_3323605154603 : Nat.Prime 3323605154603 := by
  apply nodeValid_prime [2, 97, 239, 4931, 14537] ⟨3323605154603, 2, [(2, 1), (97, 1), (239, 1), (4931, 1), (14537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_239
    · exact prime_4931
    · exact prime_14537
  · decide +kernel

theorem prime_3326546111971 : Nat.Prime 3326546111971 := by
  apply nodeValid_prime [2, 3, 5, 733, 151275403] ⟨3326546111971, 10, [(2, 1), (3, 1), (5, 1), (733, 1), (151275403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_733
    · exact prime_151275403
  · decide +kernel

theorem prime_3326546112367 : Nat.Prime 3326546112367 := by
  apply nodeValid_prime [2, 3, 71, 9421, 828871] ⟨3326546112367, 3, [(2, 1), (3, 1), (71, 1), (9421, 1), (828871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_9421
    · exact prime_828871
  · decide +kernel

theorem prime_3326546184173 : Nat.Prime 3326546184173 := by
  apply nodeValid_prime [2, 831636546043] ⟨3326546184173, 2, [(2, 2), (831636546043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_831636546043
  · decide +kernel

theorem prime_3329488887701 : Nat.Prime 3329488887701 := by
  apply nodeValid_prime [2, 5, 47, 708401891] ⟨3329488887701, 2, [(2, 2), (5, 2), (47, 1), (708401891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_708401891
  · decide +kernel

theorem prime_3329488887961 : Nat.Prime 3329488887961 := by
  apply nodeValid_prime [2, 3, 5, 277, 100165129] ⟨3329488887961, 13, [(2, 3), (3, 1), (5, 1), (277, 1), (100165129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_277
    · exact prime_100165129
  · decide +kernel

theorem prime_3329489000191 : Nat.Prime 3329489000191 := by
  apply nodeValid_prime [2, 3, 5, 110982966673] ⟨3329489000191, 3, [(2, 1), (3, 1), (5, 1), (110982966673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_110982966673
  · decide +kernel

theorem prime_3332433580943 : Nat.Prime 3332433580943 := by
  apply nodeValid_prime [2, 131, 859, 14806999] ⟨3332433580943, 5, [(2, 1), (131, 1), (859, 1), (14806999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_859
    · exact prime_14806999
  · decide +kernel

theorem prime_3332433607931 : Nat.Prime 3332433607931 := by
  apply nodeValid_prime [2, 5, 7, 53, 898230083] ⟨3332433607931, 6, [(2, 1), (5, 1), (7, 1), (53, 1), (898230083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_898230083
  · decide +kernel

theorem prime_3332433608761 : Nat.Prime 3332433608761 := by
  apply nodeValid_prime [2, 3, 5, 61, 455250493] ⟨3332433608761, 7, [(2, 3), (3, 1), (5, 1), (61, 1), (455250493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_455250493
  · decide +kernel

theorem prime_3335379935219 : Nat.Prime 3335379935219 := by
  apply nodeValid_prime [2, 397, 11491, 365567] ⟨3335379935219, 2, [(2, 1), (397, 1), (11491, 1), (365567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_11491
    · exact prime_365567
  · decide +kernel

theorem prime_3335379949841 : Nat.Prime 3335379949841 := by
  apply nodeValid_prime [2, 5, 163, 6689, 38239] ⟨3335379949841, 3, [(2, 4), (5, 1), (163, 1), (6689, 1), (38239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_163
    · exact prime_6689
    · exact prime_38239
  · decide +kernel

theorem prime_3335379951623 : Nat.Prime 3335379951623 := by
  apply nodeValid_prime [2, 97, 101159, 169957] ⟨3335379951623, 5, [(2, 1), (97, 1), (101159, 1), (169957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_101159
    · exact prime_169957
  · decide +kernel

theorem prime_3338328042971 : Nat.Prime 3338328042971 := by
  apply nodeValid_prime [2, 5, 173, 607, 3179027] ⟨3338328042971, 2, [(2, 1), (5, 1), (173, 1), (607, 1), (3179027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173
    · exact prime_607
    · exact prime_3179027
  · decide +kernel

theorem prime_3338328043481 : Nat.Prime 3338328043481 := by
  apply nodeValid_prime [2, 5, 29, 2877869003] ⟨3338328043481, 3, [(2, 3), (5, 1), (29, 1), (2877869003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_2877869003
  · decide +kernel

theorem prime_3338328048821 : Nat.Prime 3338328048821 := by
  apply nodeValid_prime [2, 5, 131, 1274171011] ⟨3338328048821, 2, [(2, 2), (5, 1), (131, 1), (1274171011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_1274171011
  · decide +kernel

theorem prime_3341277871933 : Nat.Prime 3341277871933 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 278161661] ⟨3341277871933, 6, [(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (278161661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_278161661
  · decide +kernel

theorem prime_3341277872099 : Nat.Prime 3341277872099 := by
  apply nodeValid_prime [2, 37, 45152403677] ⟨3341277872099, 2, [(2, 1), (37, 1), (45152403677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_45152403677
  · decide +kernel

theorem prime_3341277930281 : Nat.Prime 3341277930281 := by
  apply nodeValid_prime [2, 5, 229, 2003, 182111] ⟨3341277930281, 6, [(2, 3), (5, 1), (229, 1), (2003, 1), (182111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_229
    · exact prime_2003
    · exact prime_182111
  · decide +kernel

theorem prime_3344229554513 : Nat.Prime 3344229554513 := by
  apply nodeValid_prime [2, 7, 11, 929, 2921929] ⟨3344229554513, 3, [(2, 4), (7, 1), (11, 1), (929, 1), (2921929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_929
    · exact prime_2921929
  · decide +kernel

theorem prime_3344229554933 : Nat.Prime 3344229554933 := by
  apply nodeValid_prime [2, 7, 2741, 43574159] ⟨3344229554933, 2, [(2, 2), (7, 1), (2741, 1), (43574159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2741
    · exact prime_43574159
  · decide +kernel

theorem prime_3344229575333 : Nat.Prime 3344229575333 := by
  apply nodeValid_prime [2, 23, 47303, 768457] ⟨3344229575333, 2, [(2, 2), (23, 1), (47303, 1), (768457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47303
    · exact prime_768457
  · decide +kernel

theorem prime_3347182825697 : Nat.Prime 3347182825697 := by
  apply nodeValid_prime [2, 7823, 13370761] ⟨3347182825697, 3, [(2, 5), (7823, 1), (13370761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7823
    · exact prime_13370761
  · decide +kernel

theorem prime_3347182825991 : Nat.Prime 3347182825991 := by
  apply nodeValid_prime [2, 5, 55051, 6080149] ⟨3347182825991, 7, [(2, 1), (5, 1), (55051, 1), (6080149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_55051
    · exact prime_6080149
  · decide +kernel

theorem prime_3347182994299 : Nat.Prime 3347182994299 := by
  apply nodeValid_prime [2, 3, 11, 13, 12953, 301177] ⟨3347182994299, 2, [(2, 1), (3, 1), (11, 1), (13, 1), (12953, 1), (301177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_12953
    · exact prime_301177
  · decide +kernel

end Sude.Lucas.Generated
