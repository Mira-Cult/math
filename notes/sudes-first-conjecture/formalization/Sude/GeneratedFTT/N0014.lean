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
import Sude.GeneratedFTT.N0013

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1553 : Nat.Prime 1553 := by
  apply nodeValid_prime [2, 97] ⟨1553, 3, [(2, 4), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_97
  · decide +kernel

theorem prime_1873 : Nat.Prime 1873 := by
  apply nodeValid_prime [2, 3, 13] ⟨1873, 10, [(2, 4), (3, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_2251 : Nat.Prime 2251 := by
  apply nodeValid_prime [2, 3, 5] ⟨2251, 7, [(2, 1), (3, 2), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_3079 : Nat.Prime 3079 := by
  apply nodeValid_prime [2, 3, 19] ⟨3079, 6, [(2, 1), (3, 4), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_3191 : Nat.Prime 3191 := by
  apply nodeValid_prime [2, 5, 11, 29] ⟨3191, 11, [(2, 1), (5, 1), (11, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel

theorem prime_3347 : Nat.Prime 3347 := by
  apply nodeValid_prime [2, 7, 239] ⟨3347, 2, [(2, 1), (7, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_239
  · decide +kernel

theorem prime_3719 : Nat.Prime 3719 := by
  apply nodeValid_prime [2, 11, 13] ⟨3719, 7, [(2, 1), (11, 1), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_4211 : Nat.Prime 4211 := by
  apply nodeValid_prime [2, 5, 421] ⟨4211, 6, [(2, 1), (5, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_421
  · decide +kernel

theorem prime_4603 : Nat.Prime 4603 := by
  apply nodeValid_prime [2, 3, 13, 59] ⟨4603, 2, [(2, 1), (3, 1), (13, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_59
  · decide +kernel

theorem prime_4643 : Nat.Prime 4643 := by
  apply nodeValid_prime [2, 11, 211] ⟨4643, 5, [(2, 1), (11, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_211
  · decide +kernel

theorem prime_5503 : Nat.Prime 5503 := by
  apply nodeValid_prime [2, 3, 7, 131] ⟨5503, 3, [(2, 1), (3, 1), (7, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_131
  · decide +kernel

theorem prime_5851 : Nat.Prime 5851 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨5851, 2, [(2, 1), (3, 2), (5, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_6329 : Nat.Prime 6329 := by
  apply nodeValid_prime [2, 7, 113] ⟨6329, 3, [(2, 3), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_6379 : Nat.Prime 6379 := by
  apply nodeValid_prime [2, 3, 1063] ⟨6379, 2, [(2, 1), (3, 1), (1063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1063
  · decide +kernel

theorem prime_7331 : Nat.Prime 7331 := by
  apply nodeValid_prime [2, 5, 733] ⟨7331, 2, [(2, 1), (5, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_733
  · decide +kernel

theorem prime_7529 : Nat.Prime 7529 := by
  apply nodeValid_prime [2, 941] ⟨7529, 3, [(2, 3), (941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_941
  · decide +kernel

theorem prime_7583 : Nat.Prime 7583 := by
  apply nodeValid_prime [2, 17, 223] ⟨7583, 5, [(2, 1), (17, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_223
  · decide +kernel

theorem prime_8447 : Nat.Prime 8447 := by
  apply nodeValid_prime [2, 41, 103] ⟨8447, 5, [(2, 1), (41, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_103
  · decide +kernel

theorem prime_9337 : Nat.Prime 9337 := by
  apply nodeValid_prime [2, 3, 389] ⟨9337, 5, [(2, 3), (3, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
  · decide +kernel

theorem prime_9349 : Nat.Prime 9349 := by
  apply nodeValid_prime [2, 3, 19, 41] ⟨9349, 2, [(2, 2), (3, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_9473 : Nat.Prime 9473 := by
  apply nodeValid_prime [2, 37] ⟨9473, 3, [(2, 8), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37
  · decide +kernel

theorem prime_10567 : Nat.Prime 10567 := by
  apply nodeValid_prime [2, 3, 587] ⟨10567, 6, [(2, 1), (3, 2), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_587
  · decide +kernel

theorem prime_11779 : Nat.Prime 11779 := by
  apply nodeValid_prime [2, 3, 13, 151] ⟨11779, 2, [(2, 1), (3, 1), (13, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_151
  · decide +kernel

theorem prime_13513 : Nat.Prime 13513 := by
  apply nodeValid_prime [2, 3, 563] ⟨13513, 5, [(2, 3), (3, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_563
  · decide +kernel

theorem prime_13693 : Nat.Prime 13693 := by
  apply nodeValid_prime [2, 3, 7, 163] ⟨13693, 6, [(2, 2), (3, 1), (7, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_163
  · decide +kernel

theorem prime_14303 : Nat.Prime 14303 := by
  apply nodeValid_prime [2, 7151] ⟨14303, 5, [(2, 1), (7151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7151
  · decide +kernel

theorem prime_14741 : Nat.Prime 14741 := by
  apply nodeValid_prime [2, 5, 11, 67] ⟨14741, 2, [(2, 2), (5, 1), (11, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_67
  · decide +kernel

theorem prime_15493 : Nat.Prime 15493 := by
  apply nodeValid_prime [2, 3, 1291] ⟨15493, 5, [(2, 2), (3, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1291
  · decide +kernel

theorem prime_17159 : Nat.Prime 17159 := by
  apply nodeValid_prime [2, 23, 373] ⟨17159, 7, [(2, 1), (23, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_373
  · decide +kernel

theorem prime_17923 : Nat.Prime 17923 := by
  apply nodeValid_prime [2, 3, 29, 103] ⟨17923, 2, [(2, 1), (3, 1), (29, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_103
  · decide +kernel

theorem prime_18947 : Nat.Prime 18947 := by
  apply nodeValid_prime [2, 9473] ⟨18947, 2, [(2, 1), (9473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9473
  · decide +kernel

theorem prime_21751 : Nat.Prime 21751 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨21751, 3, [(2, 1), (3, 1), (5, 3), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_22871 : Nat.Prime 22871 := by
  apply nodeValid_prime [2, 5, 2287] ⟨22871, 7, [(2, 1), (5, 1), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2287
  · decide +kernel

theorem prime_26839 : Nat.Prime 26839 := by
  apply nodeValid_prime [2, 3, 7, 71] ⟨26839, 3, [(2, 1), (3, 3), (7, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
  · decide +kernel

theorem prime_27779 : Nat.Prime 27779 := by
  apply nodeValid_prime [2, 17, 19, 43] ⟨27779, 2, [(2, 1), (17, 1), (19, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_43
  · decide +kernel

theorem prime_28607 : Nat.Prime 28607 := by
  apply nodeValid_prime [2, 14303] ⟨28607, 5, [(2, 1), (14303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_14303
  · decide +kernel

theorem prime_29173 : Nat.Prime 29173 := by
  apply nodeValid_prime [2, 3, 11, 13, 17] ⟨29173, 2, [(2, 2), (3, 1), (11, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_30269 : Nat.Prime 30269 := by
  apply nodeValid_prime [2, 7, 23, 47] ⟨30269, 3, [(2, 2), (7, 1), (23, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_47
  · decide +kernel

theorem prime_31817 : Nat.Prime 31817 := by
  apply nodeValid_prime [2, 41, 97] ⟨31817, 3, [(2, 3), (41, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_97
  · decide +kernel

theorem prime_32027 : Nat.Prime 32027 := by
  apply nodeValid_prime [2, 67, 239] ⟨32027, 2, [(2, 1), (67, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_239
  · decide +kernel

theorem prime_32297 : Nat.Prime 32297 := by
  apply nodeValid_prime [2, 11, 367] ⟨32297, 3, [(2, 3), (11, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_367
  · decide +kernel

theorem prime_33569 : Nat.Prime 33569 := by
  apply nodeValid_prime [2, 1049] ⟨33569, 3, [(2, 5), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1049
  · decide +kernel

theorem prime_33619 : Nat.Prime 33619 := by
  apply nodeValid_prime [2, 3, 13, 431] ⟨33619, 2, [(2, 1), (3, 1), (13, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_431
  · decide +kernel

theorem prime_34319 : Nat.Prime 34319 := by
  apply nodeValid_prime [2, 17159] ⟨34319, 19, [(2, 1), (17159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17159
  · decide +kernel

theorem prime_40801 : Nat.Prime 40801 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨40801, 13, [(2, 5), (3, 1), (5, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_44273 : Nat.Prime 44273 := by
  apply nodeValid_prime [2, 2767] ⟨44273, 3, [(2, 4), (2767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2767
  · decide +kernel

theorem prime_44417 : Nat.Prime 44417 := by
  apply nodeValid_prime [2, 347] ⟨44417, 3, [(2, 7), (347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_347
  · decide +kernel

theorem prime_45439 : Nat.Prime 45439 := by
  apply nodeValid_prime [2, 3, 7573] ⟨45439, 3, [(2, 1), (3, 1), (7573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7573
  · decide +kernel

theorem prime_51991 : Nat.Prime 51991 := by
  apply nodeValid_prime [2, 3, 5, 1733] ⟨51991, 7, [(2, 1), (3, 1), (5, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1733
  · decide +kernel

theorem prime_55717 : Nat.Prime 55717 := by
  apply nodeValid_prime [2, 3, 4643] ⟨55717, 2, [(2, 2), (3, 1), (4643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4643
  · decide +kernel

theorem prime_65183 : Nat.Prime 65183 := by
  apply nodeValid_prime [2, 13, 23, 109] ⟨65183, 5, [(2, 1), (13, 1), (23, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_109
  · decide +kernel

theorem prime_78301 : Nat.Prime 78301 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨78301, 6, [(2, 2), (3, 3), (5, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_85717 : Nat.Prime 85717 := by
  apply nodeValid_prime [2, 3, 2381] ⟨85717, 2, [(2, 2), (3, 2), (2381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2381
  · decide +kernel

theorem prime_88547 : Nat.Prime 88547 := by
  apply nodeValid_prime [2, 44273] ⟨88547, 2, [(2, 1), (44273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44273
  · decide +kernel

theorem prime_89797 : Nat.Prime 89797 := by
  apply nodeValid_prime [2, 3, 7, 1069] ⟨89797, 5, [(2, 2), (3, 1), (7, 1), (1069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1069
  · decide +kernel

theorem prime_93371 : Nat.Prime 93371 := by
  apply nodeValid_prime [2, 5, 9337] ⟨93371, 2, [(2, 1), (5, 1), (9337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_9337
  · decide +kernel

theorem prime_102121 : Nat.Prime 102121 := by
  apply nodeValid_prime [2, 3, 5, 23, 37] ⟨102121, 7, [(2, 3), (3, 1), (5, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_113683 : Nat.Prime 113683 := by
  apply nodeValid_prime [2, 3, 18947] ⟨113683, 2, [(2, 1), (3, 1), (18947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18947
  · decide +kernel

theorem prime_130367 : Nat.Prime 130367 := by
  apply nodeValid_prime [2, 65183] ⟨130367, 5, [(2, 1), (65183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_65183
  · decide +kernel

theorem prime_135131 : Nat.Prime 135131 := by
  apply nodeValid_prime [2, 5, 13513] ⟨135131, 2, [(2, 1), (5, 1), (13513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13513
  · decide +kernel

theorem prime_151687 : Nat.Prime 151687 := by
  apply nodeValid_prime [2, 3, 53] ⟨151687, 3, [(2, 1), (3, 3), (53, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
  · decide +kernel

theorem prime_165709 : Nat.Prime 165709 := by
  apply nodeValid_prime [2, 3, 4603] ⟨165709, 2, [(2, 2), (3, 2), (4603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4603
  · decide +kernel

theorem prime_171161 : Nat.Prime 171161 := by
  apply nodeValid_prime [2, 5, 11, 389] ⟨171161, 6, [(2, 3), (5, 1), (11, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_389
  · decide +kernel

theorem prime_177739 : Nat.Prime 177739 := by
  apply nodeValid_prime [2, 3, 11, 2693] ⟨177739, 3, [(2, 1), (3, 1), (11, 1), (2693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2693
  · decide +kernel

theorem prime_183037 : Nat.Prime 183037 := by
  apply nodeValid_prime [2, 3, 7, 2179] ⟨183037, 11, [(2, 2), (3, 1), (7, 1), (2179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2179
  · decide +kernel

theorem prime_215077 : Nat.Prime 215077 := by
  apply nodeValid_prime [2, 3, 17923] ⟨215077, 2, [(2, 2), (3, 1), (17923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17923
  · decide +kernel

theorem prime_230017 : Nat.Prime 230017 := by
  apply nodeValid_prime [2, 3, 599] ⟨230017, 5, [(2, 7), (3, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_599
  · decide +kernel

theorem prime_324743 : Nat.Prime 324743 := by
  apply nodeValid_prime [2, 11, 29, 509] ⟨324743, 5, [(2, 1), (11, 1), (29, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_509
  · decide +kernel

theorem prime_461887 : Nat.Prime 461887 := by
  apply nodeValid_prime [2, 3, 23, 3347] ⟨461887, 5, [(2, 1), (3, 1), (23, 1), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3347
  · decide +kernel

theorem prime_479201 : Nat.Prime 479201 := by
  apply nodeValid_prime [2, 5, 599] ⟨479201, 3, [(2, 5), (5, 2), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_599
  · decide +kernel

theorem prime_500881 : Nat.Prime 500881 := by
  apply nodeValid_prime [2, 3, 5, 2087] ⟨500881, 7, [(2, 4), (3, 1), (5, 1), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2087
  · decide +kernel

theorem prime_523987 : Nat.Prime 523987 := by
  apply nodeValid_prime [2, 3, 23, 3797] ⟨523987, 2, [(2, 1), (3, 1), (23, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_3797
  · decide +kernel

theorem prime_593777 : Nat.Prime 593777 := by
  apply nodeValid_prime [2, 17, 37, 59] ⟨593777, 3, [(2, 4), (17, 1), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_607147 : Nat.Prime 607147 := by
  apply nodeValid_prime [2, 3, 47, 2153] ⟨607147, 2, [(2, 1), (3, 1), (47, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_2153
  · decide +kernel

theorem prime_622889 : Nat.Prime 622889 := by
  apply nodeValid_prime [2, 7, 227] ⟨622889, 6, [(2, 3), (7, 3), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_227
  · decide +kernel

theorem prime_710623 : Nat.Prime 710623 := by
  apply nodeValid_prime [2, 3, 11, 37, 97] ⟨710623, 3, [(2, 1), (3, 2), (11, 1), (37, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
    · exact prime_97
  · decide +kernel

theorem prime_726457 : Nat.Prime 726457 := by
  apply nodeValid_prime [2, 3, 30269] ⟨726457, 5, [(2, 3), (3, 1), (30269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30269
  · decide +kernel

theorem prime_728851 : Nat.Prime 728851 := by
  apply nodeValid_prime [2, 3, 5, 43, 113] ⟨728851, 3, [(2, 1), (3, 1), (5, 2), (43, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_113
  · decide +kernel

theorem prime_755233 : Nat.Prime 755233 := by
  apply nodeValid_prime [2, 3, 7867] ⟨755233, 5, [(2, 5), (3, 1), (7867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7867
  · decide +kernel

theorem prime_758111 : Nat.Prime 758111 := by
  apply nodeValid_prime [2, 5, 47, 1613] ⟨758111, 7, [(2, 1), (5, 1), (47, 1), (1613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_1613
  · decide +kernel

theorem prime_806857 : Nat.Prime 806857 := by
  apply nodeValid_prime [2, 3, 33619] ⟨806857, 5, [(2, 3), (3, 1), (33619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33619
  · decide +kernel

theorem prime_860309 : Nat.Prime 860309 := by
  apply nodeValid_prime [2, 215077] ⟨860309, 2, [(2, 2), (215077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_215077
  · decide +kernel

theorem prime_947627 : Nat.Prime 947627 := by
  apply nodeValid_prime [2, 179, 2647] ⟨947627, 2, [(2, 1), (179, 1), (2647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_2647
  · decide +kernel

theorem prime_949687 : Nat.Prime 949687 := by
  apply nodeValid_prime [2, 3, 83, 1907] ⟨949687, 3, [(2, 1), (3, 1), (83, 1), (1907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_1907
  · decide +kernel

theorem prime_1136831 : Nat.Prime 1136831 := by
  apply nodeValid_prime [2, 5, 113683] ⟨1136831, 11, [(2, 1), (5, 1), (113683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113683
  · decide +kernel

theorem prime_1245779 : Nat.Prime 1245779 := by
  apply nodeValid_prime [2, 622889] ⟨1245779, 2, [(2, 1), (622889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_622889
  · decide +kernel

theorem prime_1306817 : Nat.Prime 1306817 := by
  apply nodeValid_prime [2, 7, 2917] ⟨1306817, 3, [(2, 6), (7, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2917
  · decide +kernel

theorem prime_1327973 : Nat.Prime 1327973 := by
  apply nodeValid_prime [2, 17, 59, 331] ⟨1327973, 2, [(2, 2), (17, 1), (59, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_59
    · exact prime_331
  · decide +kernel

theorem prime_1395323 : Nat.Prime 1395323 := by
  apply nodeValid_prime [2, 19, 73, 503] ⟨1395323, 2, [(2, 1), (19, 1), (73, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_73
    · exact prime_503
  · decide +kernel

theorem prime_1719541 : Nat.Prime 1719541 := by
  apply nodeValid_prime [2, 3, 5, 41, 233] ⟨1719541, 6, [(2, 2), (3, 2), (5, 1), (41, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_233
  · decide +kernel

theorem prime_1720619 : Nat.Prime 1720619 := by
  apply nodeValid_prime [2, 860309] ⟨1720619, 2, [(2, 1), (860309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_860309
  · decide +kernel

theorem prime_2462743 : Nat.Prime 2462743 := by
  apply nodeValid_prime [2, 3, 19, 379] ⟨2462743, 3, [(2, 1), (3, 2), (19, 2), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_379
  · decide +kernel

theorem prime_2632163 : Nat.Prime 2632163 := by
  apply nodeValid_prime [2, 13, 67, 1511] ⟨2632163, 5, [(2, 1), (13, 1), (67, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_67
    · exact prime_1511
  · decide +kernel

theorem prime_2665021 : Nat.Prime 2665021 := by
  apply nodeValid_prime [2, 3, 5, 44417] ⟨2665021, 2, [(2, 2), (3, 1), (5, 1), (44417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_44417
  · decide +kernel

theorem prime_2685521 : Nat.Prime 2685521 := by
  apply nodeValid_prime [2, 5, 33569] ⟨2685521, 3, [(2, 4), (5, 1), (33569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33569
  · decide +kernel

theorem prime_2871901 : Nat.Prime 2871901 := by
  apply nodeValid_prime [2, 3, 5, 3191] ⟨2871901, 6, [(2, 2), (3, 2), (5, 2), (3191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3191
  · decide +kernel

theorem prime_3048827 : Nat.Prime 3048827 := by
  apply nodeValid_prime [2, 11, 139, 997] ⟨3048827, 2, [(2, 1), (11, 1), (139, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_139
    · exact prime_997
  · decide +kernel

theorem prime_5793743 : Nat.Prime 5793743 := by
  apply nodeValid_prime [2, 71, 40801] ⟨5793743, 5, [(2, 1), (71, 1), (40801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_40801
  · decide +kernel

theorem prime_9431767 : Nat.Prime 9431767 := by
  apply nodeValid_prime [2, 3, 523987] ⟨9431767, 3, [(2, 1), (3, 2), (523987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_523987
  · decide +kernel

theorem prime_10687987 : Nat.Prime 10687987 := by
  apply nodeValid_prime [2, 3, 593777] ⟨10687987, 5, [(2, 1), (3, 2), (593777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_593777
  · decide +kernel

theorem prime_23429633 : Nat.Prime 23429633 := by
  apply nodeValid_prime [2, 67, 683] ⟨23429633, 3, [(2, 9), (67, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_683
  · decide +kernel

theorem prime_23960051 : Nat.Prime 23960051 := by
  apply nodeValid_prime [2, 5, 479201] ⟨23960051, 2, [(2, 1), (5, 2), (479201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479201
  · decide +kernel

theorem prime_32226253 : Nat.Prime 32226253 := by
  apply nodeValid_prime [2, 3, 2685521] ⟨32226253, 2, [(2, 2), (3, 1), (2685521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2685521
  · decide +kernel

theorem prime_34762459 : Nat.Prime 34762459 := by
  apply nodeValid_prime [2, 3, 5793743] ⟨34762459, 3, [(2, 1), (3, 1), (5793743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5793743
  · decide +kernel

theorem prime_37832567 : Nat.Prime 37832567 := by
  apply nodeValid_prime [2, 53, 61, 5851] ⟨37832567, 5, [(2, 1), (53, 1), (61, 1), (5851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_61
    · exact prime_5851
  · decide +kernel

theorem prime_37882289 : Nat.Prime 37882289 := by
  apply nodeValid_prime [2, 23, 311, 331] ⟨37882289, 3, [(2, 4), (23, 1), (311, 1), (331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_311
    · exact prime_331
  · decide +kernel

theorem prime_58630463 : Nat.Prime 58630463 := by
  apply nodeValid_prime [2, 11, 2665021] ⟨58630463, 5, [(2, 1), (11, 1), (2665021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2665021
  · decide +kernel

theorem prime_62679343 : Nat.Prime 62679343 := by
  apply nodeValid_prime [2, 3, 11, 949687] ⟨62679343, 5, [(2, 1), (3, 1), (11, 1), (949687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_949687
  · decide +kernel

theorem prime_63118441 : Nat.Prime 63118441 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 23] ⟨63118441, 31, [(2, 3), (3, 4), (5, 1), (7, 1), (11, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_80684987 : Nat.Prime 80684987 := by
  apply nodeValid_prime [2, 5503, 7331] ⟨80684987, 2, [(2, 1), (5503, 1), (7331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5503
    · exact prime_7331
  · decide +kernel

theorem prime_93484957 : Nat.Prime 93484957 := by
  apply nodeValid_prime [2, 3, 227, 34319] ⟨93484957, 2, [(2, 2), (3, 1), (227, 1), (34319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_227
    · exact prime_34319
  · decide +kernel

theorem prime_94262111 : Nat.Prime 94262111 := by
  apply nodeValid_prime [2, 5, 17, 109, 5087] ⟨94262111, 13, [(2, 1), (5, 1), (17, 1), (109, 1), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_109
    · exact prime_5087
  · decide +kernel

theorem prime_99301637 : Nat.Prime 99301637 := by
  apply nodeValid_prime [2, 7, 37, 13693] ⟨99301637, 2, [(2, 2), (7, 2), (37, 1), (13693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_13693
  · decide +kernel

theorem prime_134503909 : Nat.Prime 134503909 := by
  apply nodeValid_prime [2, 3, 7, 11, 23, 6329] ⟨134503909, 2, [(2, 2), (3, 1), (7, 1), (11, 1), (23, 1), (6329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_6329
  · decide +kernel

theorem prime_139049837 : Nat.Prime 139049837 := by
  apply nodeValid_prime [2, 34762459] ⟨139049837, 2, [(2, 2), (34762459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34762459
  · decide +kernel

theorem prime_154062151 : Nat.Prime 154062151 := by
  apply nodeValid_prime [2, 3, 5, 11, 93371] ⟨154062151, 11, [(2, 1), (3, 1), (5, 2), (11, 1), (93371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_93371
  · decide +kernel

theorem prime_347881249 : Nat.Prime 347881249 := by
  apply nodeValid_prime [2, 3, 11, 13, 8447] ⟨347881249, 19, [(2, 5), (3, 2), (11, 1), (13, 1), (8447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_8447
  · decide +kernel

theorem prime_351782779 : Nat.Prime 351782779 := by
  apply nodeValid_prime [2, 3, 58630463] ⟨351782779, 2, [(2, 1), (3, 1), (58630463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58630463
  · decide +kernel

theorem prime_411879289 : Nat.Prime 411879289 := by
  apply nodeValid_prime [2, 3, 127, 135131] ⟨411879289, 7, [(2, 3), (3, 1), (127, 1), (135131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_135131
  · decide +kernel

theorem prime_453565687 : Nat.Prime 453565687 := by
  apply nodeValid_prime [2, 3, 7, 59, 183037] ⟨453565687, 3, [(2, 1), (3, 1), (7, 1), (59, 1), (183037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_59
    · exact prime_183037
  · decide +kernel

theorem prime_548268911 : Nat.Prime 548268911 := by
  apply nodeValid_prime [2, 5, 7, 109, 181, 397] ⟨548268911, 7, [(2, 1), (5, 1), (7, 1), (109, 1), (181, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_109
    · exact prime_181
    · exact prime_397
  · decide +kernel

theorem prime_1740217663 : Nat.Prime 1740217663 := by
  apply nodeValid_prime [2, 3, 32226253] ⟨1740217663, 5, [(2, 1), (3, 3), (32226253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_32226253
  · decide +kernel

theorem prime_1834792819 : Nat.Prime 1834792819 := by
  apply nodeValid_prime [2, 3, 379, 806857] ⟨1834792819, 2, [(2, 1), (3, 1), (379, 1), (806857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_806857
  · decide +kernel

theorem prime_1992919013 : Nat.Prime 1992919013 := by
  apply nodeValid_prime [2, 7, 37, 51991] ⟨1992919013, 2, [(2, 2), (7, 1), (37, 2), (51991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_51991
  · decide +kernel

theorem prime_2268066767 : Nat.Prime 2268066767 := by
  apply nodeValid_prime [2, 7, 2069, 78301] ⟨2268066767, 5, [(2, 1), (7, 1), (2069, 1), (78301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2069
    · exact prime_78301
  · decide +kernel

theorem prime_2381053237 : Nat.Prime 2381053237 := by
  apply nodeValid_prime [2, 3, 29, 67, 102121] ⟨2381053237, 2, [(2, 2), (3, 1), (29, 1), (67, 1), (102121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_67
    · exact prime_102121
  · decide +kernel

theorem prime_2669613413 : Nat.Prime 2669613413 := by
  apply nodeValid_prime [2, 271, 2462743] ⟨2669613413, 2, [(2, 2), (271, 1), (2462743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_271
    · exact prime_2462743
  · decide +kernel

theorem prime_3744255803 : Nat.Prime 3744255803 := by
  apply nodeValid_prime [2, 7, 9349, 28607] ⟨3744255803, 2, [(2, 1), (7, 1), (9349, 1), (28607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_9349
    · exact prime_28607
  · decide +kernel

theorem prime_3840898679 : Nat.Prime 3840898679 := by
  apply nodeValid_prime [2, 19, 29, 647, 5387] ⟨3840898679, 7, [(2, 1), (19, 1), (29, 1), (647, 1), (5387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_647
    · exact prime_5387
  · decide +kernel

theorem prime_13506303611 : Nat.Prime 13506303611 := by
  apply nodeValid_prime [2, 5, 443, 3048827] ⟨13506303611, 6, [(2, 1), (5, 1), (443, 1), (3048827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_443
    · exact prime_3048827
  · decide +kernel

theorem prime_40046353057 : Nat.Prime 40046353057 := by
  apply nodeValid_prime [2, 3, 139049837] ⟨40046353057, 5, [(2, 5), (3, 2), (139049837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139049837
  · decide +kernel

theorem prime_83336874473 : Nat.Prime 83336874473 := by
  apply nodeValid_prime [2, 19, 548268911] ⟨83336874473, 3, [(2, 3), (19, 1), (548268911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_548268911
  · decide +kernel

theorem prime_83724301403 : Nat.Prime 83724301403 := by
  apply nodeValid_prime [2, 7, 17, 351782779] ⟨83724301403, 2, [(2, 1), (7, 1), (17, 1), (351782779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_351782779
  · decide +kernel

theorem prime_158684015531 : Nat.Prime 158684015531 := by
  apply nodeValid_prime [2, 5, 103, 154062151] ⟨158684015531, 2, [(2, 1), (5, 1), (103, 1), (154062151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_103
    · exact prime_154062151
  · decide +kernel

theorem prime_158684015927 : Nat.Prime 158684015927 := by
  apply nodeValid_prime [2, 17, 47, 99301637] ⟨158684015927, 10, [(2, 1), (17, 1), (47, 1), (99301637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_47
    · exact prime_99301637
  · decide +kernel

theorem prime_158684017937 : Nat.Prime 158684017937 := by
  apply nodeValid_prime [2, 151, 433, 151687] ⟨158684017937, 3, [(2, 4), (151, 1), (433, 1), (151687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_433
    · exact prime_151687
  · decide +kernel

theorem prime_159058450063 : Nat.Prime 159058450063 := by
  apply nodeValid_prime [2, 3, 2111, 1395323] ⟨159058450063, 5, [(2, 1), (3, 3), (2111, 1), (1395323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2111
    · exact prime_1395323
  · decide +kernel

theorem prime_159058450697 : Nat.Prime 159058450697 := by
  apply nodeValid_prime [2, 59, 15493, 21751] ⟨159058450697, 3, [(2, 3), (59, 1), (15493, 1), (21751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_15493
    · exact prime_21751
  · decide +kernel

theorem prime_159058471321 : Nat.Prime 159058471321 := by
  apply nodeValid_prime [2, 3, 5, 7, 63118441] ⟨159058471321, 33, [(2, 3), (3, 2), (5, 1), (7, 1), (63118441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_63118441
  · decide +kernel

theorem prime_159433521041 : Nat.Prime 159433521041 := by
  apply nodeValid_prime [2, 5, 1992919013] ⟨159433521041, 6, [(2, 4), (5, 1), (1992919013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1992919013
  · decide +kernel

theorem prime_159433533911 : Nat.Prime 159433533911 := by
  apply nodeValid_prime [2, 5, 7, 37, 2909, 3023] ⟨159433533911, 7, [(2, 1), (5, 1), (7, 2), (37, 1), (2909, 1), (3023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_2909
    · exact prime_3023
  · decide +kernel

theorem prime_159433534313 : Nat.Prime 159433534313 := by
  apply nodeValid_prime [2, 13, 19, 80684987] ⟨159433534313, 5, [(2, 3), (13, 1), (19, 1), (80684987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_80684987
  · decide +kernel

theorem prime_159809163979 : Nat.Prime 159809163979 := by
  apply nodeValid_prime [2, 3, 37, 1013, 710623] ⟨159809163979, 2, [(2, 1), (3, 1), (37, 1), (1013, 1), (710623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1013
    · exact prime_710623
  · decide +kernel

theorem prime_159809164133 : Nat.Prime 159809164133 := by
  apply nodeValid_prime [2, 97, 411879289] ⟨159809164133, 2, [(2, 2), (97, 1), (411879289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_411879289
  · decide +kernel

theorem prime_159809166119 : Nat.Prime 159809166119 := by
  apply nodeValid_prime [2, 7, 463, 1873, 13163] ⟨159809166119, 7, [(2, 1), (7, 1), (463, 1), (1873, 1), (13163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_463
    · exact prime_1873
    · exact prime_13163
  · decide +kernel

theorem prime_160185412229 : Nat.Prime 160185412229 := by
  apply nodeValid_prime [2, 40046353057] ⟨160185412229, 2, [(2, 2), (40046353057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_40046353057
  · decide +kernel

theorem prime_160185415079 : Nat.Prime 160185415079 := by
  apply nodeValid_prime [2, 13, 79, 107, 728851] ⟨160185415079, 7, [(2, 1), (13, 1), (79, 1), (107, 1), (728851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_79
    · exact prime_107
    · exact prime_728851
  · decide +kernel

theorem prime_160185415153 : Nat.Prime 160185415153 := by
  apply nodeValid_prime [2, 3, 7, 359, 1327973] ⟨160185415153, 5, [(2, 4), (3, 1), (7, 1), (359, 1), (1327973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_359
    · exact prime_1327973
  · decide +kernel

theorem prime_160562241109 : Nat.Prime 160562241109 := by
  apply nodeValid_prime [2, 3, 1553, 2871901] ⟨160562241109, 2, [(2, 2), (3, 2), (1553, 1), (2871901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1553
    · exact prime_2871901
  · decide +kernel

theorem prime_160562241883 : Nat.Prime 160562241883 := by
  apply nodeValid_prime [2, 3, 7, 22871, 55717] ⟨160562241883, 17, [(2, 1), (3, 2), (7, 1), (22871, 1), (55717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_22871
    · exact prime_55717
  · decide +kernel

theorem prime_160562253199 : Nat.Prime 160562253199 := by
  apply nodeValid_prime [2, 3, 59, 453565687] ⟨160562253199, 6, [(2, 1), (3, 1), (59, 1), (453565687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_453565687
  · decide +kernel

theorem prime_160939697453 : Nat.Prime 160939697453 := by
  apply nodeValid_prime [2, 32297, 1245779] ⟨160939697453, 2, [(2, 2), (32297, 1), (1245779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_32297
    · exact prime_1245779
  · decide +kernel

theorem prime_160939707437 : Nat.Prime 160939707437 := by
  apply nodeValid_prime [2, 29, 541, 1069, 2399] ⟨160939707437, 2, [(2, 2), (29, 1), (541, 1), (1069, 1), (2399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_541
    · exact prime_1069
    · exact prime_2399
  · decide +kernel

theorem prime_160939708247 : Nat.Prime 160939708247 := by
  apply nodeValid_prime [2, 7529, 10687987] ⟨160939708247, 5, [(2, 1), (7529, 1), (10687987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7529
    · exact prime_10687987
  · decide +kernel

theorem prime_161317741909 : Nat.Prime 161317741909 := by
  apply nodeValid_prime [2, 3, 26839, 500881] ⟨161317741909, 2, [(2, 2), (3, 1), (26839, 1), (500881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_26839
    · exact prime_500881
  · decide +kernel

theorem prime_161317743607 : Nat.Prime 161317743607 := by
  apply nodeValid_prime [2, 3, 29, 509, 607147] ⟨161317743607, 3, [(2, 1), (3, 2), (29, 1), (509, 1), (607147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_509
    · exact prime_607147
  · decide +kernel

theorem prime_161317744519 : Nat.Prime 161317744519 := by
  apply nodeValid_prime [2, 3, 7, 3840898679] ⟨161317744519, 3, [(2, 1), (3, 1), (7, 1), (3840898679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3840898679
  · decide +kernel

theorem prime_161696385077 : Nat.Prime 161696385077 := by
  apply nodeValid_prime [2, 23, 863, 88547] ⟨161696385077, 2, [(2, 2), (23, 2), (863, 1), (88547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_863
    · exact prime_88547
  · decide +kernel

theorem prime_161696385313 : Nat.Prime 161696385313 := by
  apply nodeValid_prime [2, 3, 7, 11, 37, 131, 4513] ⟨161696385313, 5, [(2, 5), (3, 1), (7, 1), (11, 1), (37, 1), (131, 1), (4513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_37
    · exact prime_131
    · exact prime_4513
  · decide +kernel

theorem prime_161696391359 : Nat.Prime 161696391359 := by
  apply nodeValid_prime [2, 2137, 37832567] ⟨161696391359, 19, [(2, 1), (2137, 1), (37832567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2137
    · exact prime_37832567
  · decide +kernel

theorem prime_162075642119 : Nat.Prime 162075642119 := by
  apply nodeValid_prime [2, 13, 239, 2251, 11587] ⟨162075642119, 29, [(2, 1), (13, 1), (239, 1), (2251, 1), (11587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_239
    · exact prime_2251
    · exact prime_11587
  · decide +kernel

theorem prime_162075643333 : Nat.Prime 162075643333 := by
  apply nodeValid_prime [2, 3, 13506303611] ⟨162075643333, 2, [(2, 2), (3, 1), (13506303611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13506303611
  · decide +kernel

theorem prime_162075643943 : Nat.Prime 162075643943 := by
  apply nodeValid_prime [2, 113, 5501, 130367] ⟨162075643943, 5, [(2, 1), (113, 1), (5501, 1), (130367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_5501
    · exact prime_130367
  · decide +kernel

theorem prime_162455486693 : Nat.Prime 162455486693 := by
  apply nodeValid_prime [2, 317, 557, 230017] ⟨162455486693, 2, [(2, 2), (317, 1), (557, 1), (230017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_557
    · exact prime_230017
  · decide +kernel

theorem prime_162455487119 : Nat.Prime 162455487119 := by
  apply nodeValid_prime [2, 85717, 947627] ⟨162455487119, 7, [(2, 1), (85717, 1), (947627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_85717
    · exact prime_947627
  · decide +kernel

theorem prime_162455492707 : Nat.Prime 162455492707 := by
  apply nodeValid_prime [2, 3, 13, 281, 1993, 3719] ⟨162455492707, 2, [(2, 1), (3, 1), (13, 1), (281, 1), (1993, 1), (3719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_281
    · exact prime_1993
    · exact prime_3719
  · decide +kernel

theorem prime_162835940329 : Nat.Prime 162835940329 := by
  apply nodeValid_prime [2, 3, 59, 647, 177739] ⟨162835940329, 7, [(2, 3), (3, 1), (59, 1), (647, 1), (177739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_647
    · exact prime_177739
  · decide +kernel

theorem prime_162835940923 : Nat.Prime 162835940923 := by
  apply nodeValid_prime [2, 3, 15773, 1720619] ⟨162835940923, 2, [(2, 1), (3, 1), (15773, 1), (1720619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15773
    · exact prime_1720619
  · decide +kernel

theorem prime_162835949351 : Nat.Prime 162835949351 := by
  apply nodeValid_prime [2, 5, 139, 23429633] ⟨162835949351, 11, [(2, 1), (5, 2), (139, 1), (23429633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_23429633
  · decide +kernel

theorem prime_163217009173 : Nat.Prime 163217009173 := by
  apply nodeValid_prime [2, 3, 7, 31, 62679343] ⟨163217009173, 2, [(2, 2), (3, 1), (7, 1), (31, 1), (62679343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_62679343
  · decide +kernel

theorem prime_163217009191 : Nat.Prime 163217009191 := by
  apply nodeValid_prime [2, 3, 5, 11779, 461887] ⟨163217009191, 3, [(2, 1), (3, 1), (5, 1), (11779, 1), (461887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11779
    · exact prime_461887
  · decide +kernel

theorem prime_163217010157 : Nat.Prime 163217010157 := by
  apply nodeValid_prime [2, 3, 29, 14741, 31817] ⟨163217010157, 2, [(2, 2), (3, 1), (29, 1), (14741, 1), (31817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_14741
    · exact prime_31817
  · decide +kernel

theorem prime_163598671009 : Nat.Prime 163598671009 := by
  apply nodeValid_prime [2, 3, 23, 41, 43, 14009] ⟨163598671009, 13, [(2, 5), (3, 2), (23, 1), (41, 1), (43, 1), (14009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_43
    · exact prime_14009
  · decide +kernel

theorem prime_163598674751 : Nat.Prime 163598674751 := by
  apply nodeValid_prime [2, 5, 7, 93484957] ⟨163598674751, 7, [(2, 1), (5, 3), (7, 1), (93484957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_93484957
  · decide +kernel

theorem prime_163598674907 : Nat.Prime 163598674907 := by
  apply nodeValid_prime [2, 19, 199, 1601, 13513] ⟨163598674907, 2, [(2, 1), (19, 1), (199, 1), (1601, 1), (13513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_199
    · exact prime_1601
    · exact prime_13513
  · decide +kernel

theorem prime_163980925523 : Nat.Prime 163980925523 := by
  apply nodeValid_prime [2, 37, 79, 758111] ⟨163980925523, 2, [(2, 1), (37, 2), (79, 1), (758111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_79
    · exact prime_758111
  · decide +kernel

theorem prime_163980926309 : Nat.Prime 163980926309 := by
  apply nodeValid_prime [2, 41, 3079, 324743] ⟨163980926309, 2, [(2, 2), (41, 1), (3079, 1), (324743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_3079
    · exact prime_324743
  · decide +kernel

theorem prime_163980934231 : Nat.Prime 163980934231 := by
  apply nodeValid_prime [2, 3, 5, 113, 6379, 7583] ⟨163980934231, 6, [(2, 1), (3, 1), (5, 1), (113, 1), (6379, 1), (7583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_6379
    · exact prime_7583
  · decide +kernel

theorem prime_164363774339 : Nat.Prime 164363774339 := by
  apply nodeValid_prime [2, 17, 29173, 165709] ⟨164363774339, 2, [(2, 1), (17, 1), (29173, 1), (165709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29173
    · exact prime_165709
  · decide +kernel

theorem prime_164363776799 : Nat.Prime 164363776799 := by
  apply nodeValid_prime [2, 13, 47, 134503909] ⟨164363776799, 23, [(2, 1), (13, 1), (47, 1), (134503909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
    · exact prime_134503909
  · decide +kernel

theorem prime_164363802079 : Nat.Prime 164363802079 := by
  apply nodeValid_prime [2, 3, 7, 5387, 726457] ⟨164363802079, 6, [(2, 1), (3, 1), (7, 1), (5387, 1), (726457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5387
    · exact prime_726457
  · decide +kernel

theorem prime_164747255009 : Nat.Prime 164747255009 := by
  apply nodeValid_prime [2, 7, 4297, 171161] ⟨164747255009, 3, [(2, 5), (7, 1), (4297, 1), (171161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4297
    · exact prime_171161
  · decide +kernel

theorem prime_164747255333 : Nat.Prime 164747255333 := by
  apply nodeValid_prime [2, 11, 3744255803] ⟨164747255333, 2, [(2, 2), (11, 1), (3744255803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3744255803
  · decide +kernel

theorem prime_164747274859 : Nat.Prime 164747274859 := by
  apply nodeValid_prime [2, 3, 83, 97, 1136831] ⟨164747274859, 2, [(2, 1), (3, 2), (83, 1), (97, 1), (1136831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_97
    · exact prime_1136831
  · decide +kernel

theorem prime_165131353711 : Nat.Prime 165131353711 := by
  apply nodeValid_prime [2, 3, 5, 1834792819] ⟨165131353711, 14, [(2, 1), (3, 2), (5, 1), (1834792819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1834792819
  · decide +kernel

theorem prime_165131376637 : Nat.Prime 165131376637 := by
  apply nodeValid_prime [2, 3, 1459, 9431767] ⟨165131376637, 2, [(2, 2), (3, 1), (1459, 1), (9431767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1459
    · exact prime_9431767
  · decide +kernel

theorem prime_165131377969 : Nat.Prime 165131377969 := by
  apply nodeValid_prime [2, 3, 1307, 2632163] ⟨165131377969, 11, [(2, 4), (3, 1), (1307, 1), (2632163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1307
    · exact prime_2632163
  · decide +kernel

theorem prime_165516031607 : Nat.Prime 165516031607 := by
  apply nodeValid_prime [2, 31, 2669613413] ⟨165516031607, 5, [(2, 1), (31, 1), (2669613413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_2669613413
  · decide +kernel

theorem prime_165516032309 : Nat.Prime 165516032309 := by
  apply nodeValid_prime [2, 11, 157, 23960051] ⟨165516032309, 2, [(2, 2), (11, 1), (157, 1), (23960051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_157
    · exact prime_23960051
  · decide +kernel

theorem prime_165516041861 : Nat.Prime 165516041861 := by
  apply nodeValid_prime [2, 5, 13, 239, 281, 9479] ⟨165516041861, 14, [(2, 2), (5, 1), (13, 1), (239, 1), (281, 1), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_239
    · exact prime_281
    · exact prime_9479
  · decide +kernel

theorem prime_165901315361 : Nat.Prime 165901315361 := by
  apply nodeValid_prime [2, 5, 11, 94262111] ⟨165901315361, 6, [(2, 5), (5, 1), (11, 1), (94262111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_94262111
  · decide +kernel

theorem prime_165901315681 : Nat.Prime 165901315681 := by
  apply nodeValid_prime [2, 3, 5, 67, 1719541] ⟨165901315681, 7, [(2, 5), (3, 2), (5, 1), (67, 1), (1719541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
    · exact prime_1719541
  · decide +kernel

theorem prime_165901333243 : Nat.Prime 165901333243 := by
  apply nodeValid_prime [2, 3, 19, 32027, 45439] ⟨165901333243, 2, [(2, 1), (3, 1), (19, 1), (32027, 1), (45439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_32027
    · exact prime_45439
  · decide +kernel

theorem prime_166287213451 : Nat.Prime 166287213451 := by
  apply nodeValid_prime [2, 3, 5, 277, 761, 1753] ⟨166287213451, 2, [(2, 1), (3, 2), (5, 2), (277, 1), (761, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_277
    · exact prime_761
    · exact prime_1753
  · decide +kernel

theorem prime_166287215089 : Nat.Prime 166287215089 := by
  apply nodeValid_prime [2, 3, 73, 499, 10567] ⟨166287215089, 22, [(2, 4), (3, 3), (73, 1), (499, 1), (10567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_499
    · exact prime_10567
  · decide +kernel

theorem prime_166287237023 : Nat.Prime 166287237023 := by
  apply nodeValid_prime [2, 239, 347881249] ⟨166287237023, 5, [(2, 1), (239, 1), (347881249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_239
    · exact prime_347881249
  · decide +kernel

theorem prime_166673726591 : Nat.Prime 166673726591 := by
  apply nodeValid_prime [2, 5, 7, 2381053237] ⟨166673726591, 11, [(2, 1), (5, 1), (7, 1), (2381053237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2381053237
  · decide +kernel

theorem prime_166673727119 : Nat.Prime 166673727119 := by
  apply nodeValid_prime [2, 139, 1789, 2411] ⟨166673727119, 7, [(2, 1), (139, 2), (1789, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_1789
    · exact prime_2411
  · decide +kernel

theorem prime_166673748947 : Nat.Prime 166673748947 := by
  apply nodeValid_prime [2, 83336874473] ⟨166673748947, 2, [(2, 1), (83336874473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_83336874473
  · decide +kernel

theorem prime_167060871647 : Nat.Prime 167060871647 := by
  apply nodeValid_prime [2, 41, 1559, 1306817] ⟨167060871647, 5, [(2, 1), (41, 1), (1559, 1), (1306817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1559
    · exact prime_1306817
  · decide +kernel

theorem prime_167060894491 : Nat.Prime 167060894491 := by
  apply nodeValid_prime [2, 3, 5, 7, 37882289] ⟨167060894491, 2, [(2, 1), (3, 2), (5, 1), (7, 2), (37882289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37882289
  · decide +kernel

theorem prime_167060895649 : Nat.Prime 167060895649 := by
  apply nodeValid_prime [2, 3, 1740217663] ⟨167060895649, 11, [(2, 5), (3, 1), (1740217663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1740217663
  · decide +kernel

theorem prime_167448595849 : Nat.Prime 167448595849 := by
  apply nodeValid_prime [2, 3, 19, 29, 31, 97, 4211] ⟨167448595849, 7, [(2, 3), (3, 1), (19, 1), (29, 1), (31, 1), (97, 1), (4211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_29
    · exact prime_31
    · exact prime_97
    · exact prime_4211
  · decide +kernel

theorem prime_167448596563 : Nat.Prime 167448596563 := by
  apply nodeValid_prime [2, 3, 13, 613, 89797] ⟨167448596563, 3, [(2, 1), (3, 2), (13, 2), (613, 1), (89797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_613
    · exact prime_89797
  · decide +kernel

theorem prime_167448602807 : Nat.Prime 167448602807 := by
  apply nodeValid_prime [2, 83724301403] ⟨167448602807, 5, [(2, 1), (83724301403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_83724301403
  · decide +kernel

theorem prime_167836940057 : Nat.Prime 167836940057 := by
  apply nodeValid_prime [2, 27779, 755233] ⟨167836940057, 3, [(2, 3), (27779, 1), (755233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_27779
    · exact prime_755233
  · decide +kernel

theorem prime_167836940759 : Nat.Prime 167836940759 := by
  apply nodeValid_prime [2, 37, 2268066767] ⟨167836940759, 11, [(2, 1), (37, 1), (2268066767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2268066767
  · decide +kernel

end Sude.Lucas.Generated
