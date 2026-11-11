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

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_1523 : Nat.Prime 1523 := by
  apply nodeValid_prime [2, 761] ⟨1523, 2, [(2, 1), (761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_761
  · decide +kernel

theorem prime_2417 : Nat.Prime 2417 := by
  apply nodeValid_prime [2, 151] ⟨2417, 3, [(2, 4), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_151
  · decide +kernel

theorem prime_2521 : Nat.Prime 2521 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨2521, 17, [(2, 3), (3, 2), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_2671 : Nat.Prime 2671 := by
  apply nodeValid_prime [2, 3, 5, 89] ⟨2671, 7, [(2, 1), (3, 1), (5, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
  · decide +kernel

theorem prime_3583 : Nat.Prime 3583 := by
  apply nodeValid_prime [2, 3, 199] ⟨3583, 3, [(2, 1), (3, 2), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
  · decide +kernel

theorem prime_3637 : Nat.Prime 3637 := by
  apply nodeValid_prime [2, 3, 101] ⟨3637, 2, [(2, 2), (3, 2), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_3797 : Nat.Prime 3797 := by
  apply nodeValid_prime [2, 13, 73] ⟨3797, 2, [(2, 2), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_3803 : Nat.Prime 3803 := by
  apply nodeValid_prime [2, 1901] ⟨3803, 2, [(2, 1), (1901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1901
  · decide +kernel

theorem prime_4493 : Nat.Prime 4493 := by
  apply nodeValid_prime [2, 1123] ⟨4493, 2, [(2, 2), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1123
  · decide +kernel

theorem prime_4583 : Nat.Prime 4583 := by
  apply nodeValid_prime [2, 29, 79] ⟨4583, 5, [(2, 1), (29, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_79
  · decide +kernel

theorem prime_4663 : Nat.Prime 4663 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨4663, 3, [(2, 1), (3, 2), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_4817 : Nat.Prime 4817 := by
  apply nodeValid_prime [2, 7, 43] ⟨4817, 3, [(2, 4), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_5171 : Nat.Prime 5171 := by
  apply nodeValid_prime [2, 5, 11, 47] ⟨5171, 2, [(2, 1), (5, 1), (11, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_47
  · decide +kernel

theorem prime_5471 : Nat.Prime 5471 := by
  apply nodeValid_prime [2, 5, 547] ⟨5471, 7, [(2, 1), (5, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_547
  · decide +kernel

theorem prime_6037 : Nat.Prime 6037 := by
  apply nodeValid_prime [2, 3, 503] ⟨6037, 5, [(2, 2), (3, 1), (503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_503
  · decide +kernel

theorem prime_6571 : Nat.Prime 6571 := by
  apply nodeValid_prime [2, 3, 5, 73] ⟨6571, 3, [(2, 1), (3, 2), (5, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
  · decide +kernel

theorem prime_7159 : Nat.Prime 7159 := by
  apply nodeValid_prime [2, 3, 1193] ⟨7159, 3, [(2, 1), (3, 1), (1193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1193
  · decide +kernel

theorem prime_7177 : Nat.Prime 7177 := by
  apply nodeValid_prime [2, 3, 13, 23] ⟨7177, 10, [(2, 3), (3, 1), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_7607 : Nat.Prime 7607 := by
  apply nodeValid_prime [2, 3803] ⟨7607, 5, [(2, 1), (3803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3803
  · decide +kernel

theorem prime_7723 : Nat.Prime 7723 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨7723, 3, [(2, 1), (3, 3), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_8233 : Nat.Prime 8233 := by
  apply nodeValid_prime [2, 3, 7] ⟨8233, 10, [(2, 3), (3, 1), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_9371 : Nat.Prime 9371 := by
  apply nodeValid_prime [2, 5, 937] ⟨9371, 2, [(2, 1), (5, 1), (937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_937
  · decide +kernel

theorem prime_10247 : Nat.Prime 10247 := by
  apply nodeValid_prime [2, 47, 109] ⟨10247, 5, [(2, 1), (47, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_109
  · decide +kernel

theorem prime_10781 : Nat.Prime 10781 := by
  apply nodeValid_prime [2, 5, 7, 11] ⟨10781, 10, [(2, 2), (5, 1), (7, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_11093 : Nat.Prime 11093 := by
  apply nodeValid_prime [2, 47, 59] ⟨11093, 2, [(2, 2), (47, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_59
  · decide +kernel

theorem prime_13291 : Nat.Prime 13291 := by
  apply nodeValid_prime [2, 3, 5, 443] ⟨13291, 2, [(2, 1), (3, 1), (5, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_443
  · decide +kernel

theorem prime_13723 : Nat.Prime 13723 := by
  apply nodeValid_prime [2, 3, 2287] ⟨13723, 2, [(2, 1), (3, 1), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2287
  · decide +kernel

theorem prime_14653 : Nat.Prime 14653 := by
  apply nodeValid_prime [2, 3, 11, 37] ⟨14653, 2, [(2, 2), (3, 2), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_15451 : Nat.Prime 15451 := by
  apply nodeValid_prime [2, 3, 5, 103] ⟨15451, 3, [(2, 1), (3, 1), (5, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_103
  · decide +kernel

theorem prime_16231 : Nat.Prime 16231 := by
  apply nodeValid_prime [2, 3, 5, 541] ⟨16231, 3, [(2, 1), (3, 1), (5, 1), (541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_541
  · decide +kernel

theorem prime_18133 : Nat.Prime 18133 := by
  apply nodeValid_prime [2, 3, 1511] ⟨18133, 5, [(2, 2), (3, 1), (1511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1511
  · decide +kernel

theorem prime_18517 : Nat.Prime 18517 := by
  apply nodeValid_prime [2, 3, 1543] ⟨18517, 6, [(2, 2), (3, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1543
  · decide +kernel

theorem prime_18583 : Nat.Prime 18583 := by
  apply nodeValid_prime [2, 3, 19, 163] ⟨18583, 3, [(2, 1), (3, 1), (19, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_163
  · decide +kernel

theorem prime_20269 : Nat.Prime 20269 := by
  apply nodeValid_prime [2, 3, 563] ⟨20269, 2, [(2, 2), (3, 2), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_563
  · decide +kernel

theorem prime_20551 : Nat.Prime 20551 := by
  apply nodeValid_prime [2, 3, 5, 137] ⟨20551, 3, [(2, 1), (3, 1), (5, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_21401 : Nat.Prime 21401 := by
  apply nodeValid_prime [2, 5, 107] ⟨21401, 3, [(2, 3), (5, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_24677 : Nat.Prime 24677 := by
  apply nodeValid_prime [2, 31, 199] ⟨24677, 2, [(2, 2), (31, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_199
  · decide +kernel

theorem prime_30253 : Nat.Prime 30253 := by
  apply nodeValid_prime [2, 3, 2521] ⟨30253, 2, [(2, 2), (3, 1), (2521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2521
  · decide +kernel

theorem prime_34511 : Nat.Prime 34511 := by
  apply nodeValid_prime [2, 5, 7, 17, 29] ⟨34511, 7, [(2, 1), (5, 1), (7, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_34819 : Nat.Prime 34819 := by
  apply nodeValid_prime [2, 3, 7, 829] ⟨34819, 2, [(2, 1), (3, 1), (7, 1), (829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_829
  · decide +kernel

theorem prime_36677 : Nat.Prime 36677 := by
  apply nodeValid_prime [2, 53, 173] ⟨36677, 2, [(2, 2), (53, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_173
  · decide +kernel

theorem prime_41617 : Nat.Prime 41617 := by
  apply nodeValid_prime [2, 3, 17] ⟨41617, 5, [(2, 4), (3, 2), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_50341 : Nat.Prime 50341 := by
  apply nodeValid_prime [2, 3, 5, 839] ⟨50341, 2, [(2, 2), (3, 1), (5, 1), (839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_839
  · decide +kernel

theorem prime_52457 : Nat.Prime 52457 := by
  apply nodeValid_prime [2, 79, 83] ⟨52457, 3, [(2, 3), (79, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_83
  · decide +kernel

theorem prime_58693 : Nat.Prime 58693 := by
  apply nodeValid_prime [2, 3, 67, 73] ⟨58693, 2, [(2, 2), (3, 1), (67, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_73
  · decide +kernel

theorem prime_61559 : Nat.Prime 61559 := by
  apply nodeValid_prime [2, 7, 4397] ⟨61559, 7, [(2, 1), (7, 1), (4397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4397
  · decide +kernel

theorem prime_62119 : Nat.Prime 62119 := by
  apply nodeValid_prime [2, 3, 7, 17, 29] ⟨62119, 7, [(2, 1), (3, 2), (7, 1), (17, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_65327 : Nat.Prime 65327 := by
  apply nodeValid_prime [2, 89, 367] ⟨65327, 5, [(2, 1), (89, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_367
  · decide +kernel

theorem prime_74609 : Nat.Prime 74609 := by
  apply nodeValid_prime [2, 4663] ⟨74609, 3, [(2, 4), (4663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4663
  · decide +kernel

theorem prime_76481 : Nat.Prime 76481 := by
  apply nodeValid_prime [2, 5, 239] ⟨76481, 3, [(2, 6), (5, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_239
  · decide +kernel

theorem prime_84121 : Nat.Prime 84121 := by
  apply nodeValid_prime [2, 3, 5, 701] ⟨84121, 13, [(2, 3), (3, 1), (5, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_701
  · decide +kernel

theorem prime_88789 : Nat.Prime 88789 := by
  apply nodeValid_prime [2, 3, 7, 151] ⟨88789, 2, [(2, 2), (3, 1), (7, 2), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_151
  · decide +kernel

theorem prime_93629 : Nat.Prime 93629 := by
  apply nodeValid_prime [2, 89, 263] ⟨93629, 2, [(2, 2), (89, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_263
  · decide +kernel

theorem prime_112303 : Nat.Prime 112303 := by
  apply nodeValid_prime [2, 3, 17, 367] ⟨112303, 3, [(2, 1), (3, 2), (17, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_367
  · decide +kernel

theorem prime_118901 : Nat.Prime 118901 := by
  apply nodeValid_prime [2, 5, 29, 41] ⟨118901, 2, [(2, 2), (5, 2), (29, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_41
  · decide +kernel

theorem prime_144563 : Nat.Prime 144563 := by
  apply nodeValid_prime [2, 11, 6571] ⟨144563, 2, [(2, 1), (11, 1), (6571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_6571
  · decide +kernel

theorem prime_153427 : Nat.Prime 153427 := by
  apply nodeValid_prime [2, 3, 7, 13, 281] ⟨153427, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_281
  · decide +kernel

theorem prime_164677 : Nat.Prime 164677 := by
  apply nodeValid_prime [2, 3, 13723] ⟨164677, 2, [(2, 2), (3, 1), (13723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13723
  · decide +kernel

theorem prime_171757 : Nat.Prime 171757 := by
  apply nodeValid_prime [2, 3, 13, 367] ⟨171757, 7, [(2, 2), (3, 2), (13, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_367
  · decide +kernel

theorem prime_180371 : Nat.Prime 180371 := by
  apply nodeValid_prime [2, 5, 17, 1061] ⟨180371, 7, [(2, 1), (5, 1), (17, 1), (1061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1061
  · decide +kernel

theorem prime_194749 : Nat.Prime 194749 := by
  apply nodeValid_prime [2, 3, 16229] ⟨194749, 2, [(2, 2), (3, 1), (16229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16229
  · decide +kernel

theorem prime_273157 : Nat.Prime 273157 := by
  apply nodeValid_prime [2, 3, 13, 17, 103] ⟨273157, 5, [(2, 2), (3, 1), (13, 1), (17, 1), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_103
  · decide +kernel

theorem prime_300973 : Nat.Prime 300973 := by
  apply nodeValid_prime [2, 3, 7, 3583] ⟨300973, 2, [(2, 2), (3, 1), (7, 1), (3583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3583
  · decide +kernel

theorem prime_332779 : Nat.Prime 332779 := by
  apply nodeValid_prime [2, 3, 37, 1499] ⟨332779, 2, [(2, 1), (3, 1), (37, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1499
  · decide +kernel

theorem prime_383549 : Nat.Prime 383549 := by
  apply nodeValid_prime [2, 11, 23, 379] ⟨383549, 2, [(2, 2), (11, 1), (23, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_379
  · decide +kernel

theorem prime_394577 : Nat.Prime 394577 := by
  apply nodeValid_prime [2, 7, 13, 271] ⟨394577, 3, [(2, 4), (7, 1), (13, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_271
  · decide +kernel

theorem prime_432923 : Nat.Prime 432923 := by
  apply nodeValid_prime [2, 7, 17, 107] ⟨432923, 2, [(2, 1), (7, 1), (17, 2), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_107
  · decide +kernel

theorem prime_518159 : Nat.Prime 518159 := by
  apply nodeValid_prime [2, 41, 71, 89] ⟨518159, 11, [(2, 1), (41, 1), (71, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_71
    · exact prime_89
  · decide +kernel

theorem prime_564881 : Nat.Prime 564881 := by
  apply nodeValid_prime [2, 5, 23, 307] ⟨564881, 3, [(2, 4), (5, 1), (23, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_307
  · decide +kernel

theorem prime_614483 : Nat.Prime 614483 := by
  apply nodeValid_prime [2, 11, 17, 31, 53] ⟨614483, 2, [(2, 1), (11, 1), (17, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_667687 : Nat.Prime 667687 := by
  apply nodeValid_prime [2, 3, 257, 433] ⟨667687, 3, [(2, 1), (3, 1), (257, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_257
    · exact prime_433
  · decide +kernel

theorem prime_680203 : Nat.Prime 680203 := by
  apply nodeValid_prime [2, 3, 23, 31, 53] ⟨680203, 12, [(2, 1), (3, 2), (23, 1), (31, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_31
    · exact prime_53
  · decide +kernel

theorem prime_709097 : Nat.Prime 709097 := by
  apply nodeValid_prime [2, 151, 587] ⟨709097, 3, [(2, 3), (151, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_587
  · decide +kernel

theorem prime_741409 : Nat.Prime 741409 := by
  apply nodeValid_prime [2, 3, 7723] ⟨741409, 13, [(2, 5), (3, 1), (7723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7723
  · decide +kernel

theorem prime_755879 : Nat.Prime 755879 := by
  apply nodeValid_prime [2, 457, 827] ⟨755879, 11, [(2, 1), (457, 1), (827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_457
    · exact prime_827
  · decide +kernel

theorem prime_865847 : Nat.Prime 865847 := by
  apply nodeValid_prime [2, 432923] ⟨865847, 5, [(2, 1), (432923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_432923
  · decide +kernel

theorem prime_984497 : Nat.Prime 984497 := by
  apply nodeValid_prime [2, 37, 1663] ⟨984497, 3, [(2, 4), (37, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1663
  · decide +kernel

theorem prime_1036319 : Nat.Prime 1036319 := by
  apply nodeValid_prime [2, 518159] ⟨1036319, 7, [(2, 1), (518159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_518159
  · decide +kernel

theorem prime_1082153 : Nat.Prime 1082153 := by
  apply nodeValid_prime [2, 17, 73, 109] ⟨1082153, 3, [(2, 3), (17, 1), (73, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_73
    · exact prime_109
  · decide +kernel

theorem prime_1087981 : Nat.Prime 1087981 := by
  apply nodeValid_prime [2, 3, 5, 18133] ⟨1087981, 2, [(2, 2), (3, 1), (5, 1), (18133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_18133
  · decide +kernel

theorem prime_1310807 : Nat.Prime 1310807 := by
  apply nodeValid_prime [2, 7, 93629] ⟨1310807, 10, [(2, 1), (7, 1), (93629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_93629
  · decide +kernel

theorem prime_1434497 : Nat.Prime 1434497 := by
  apply nodeValid_prime [2, 7, 1601] ⟨1434497, 3, [(2, 7), (7, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1601
  · decide +kernel

theorem prime_1492181 : Nat.Prime 1492181 := by
  apply nodeValid_prime [2, 5, 74609] ⟨1492181, 2, [(2, 2), (5, 1), (74609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_74609
  · decide +kernel

theorem prime_1560709 : Nat.Prime 1560709 := by
  apply nodeValid_prime [2, 3, 4817] ⟨1560709, 2, [(2, 2), (3, 4), (4817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4817
  · decide +kernel

theorem prime_2031571 : Nat.Prime 2031571 := by
  apply nodeValid_prime [2, 3, 5, 22573] ⟨2031571, 2, [(2, 1), (3, 2), (5, 1), (22573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_22573
  · decide +kernel

theorem prime_2082163 : Nat.Prime 2082163 := by
  apply nodeValid_prime [2, 3, 163, 2129] ⟨2082163, 2, [(2, 1), (3, 1), (163, 1), (2129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_2129
  · decide +kernel

theorem prime_2138503 : Nat.Prime 2138503 := by
  apply nodeValid_prime [2, 3, 107, 3331] ⟨2138503, 11, [(2, 1), (3, 1), (107, 1), (3331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_3331
  · decide +kernel

theorem prime_2707039 : Nat.Prime 2707039 := by
  apply nodeValid_prime [2, 3, 59, 2549] ⟨2707039, 3, [(2, 1), (3, 2), (59, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_2549
  · decide +kernel

theorem prime_2832679 : Nat.Prime 2832679 := by
  apply nodeValid_prime [2, 3, 52457] ⟨2832679, 3, [(2, 1), (3, 3), (52457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52457
  · decide +kernel

theorem prime_2855159 : Nat.Prime 2855159 := by
  apply nodeValid_prime [2, 41, 34819] ⟨2855159, 13, [(2, 1), (41, 1), (34819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_34819
  · decide +kernel

theorem prime_3507971 : Nat.Prime 3507971 := by
  apply nodeValid_prime [2, 5, 19, 37, 499] ⟨3507971, 2, [(2, 1), (5, 1), (19, 1), (37, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_37
    · exact prime_499
  · decide +kernel

theorem prime_4114193 : Nat.Prime 4114193 := by
  apply nodeValid_prime [2, 47, 5471] ⟨4114193, 3, [(2, 4), (47, 1), (5471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_5471
  · decide +kernel

theorem prime_4808327 : Nat.Prime 4808327 := by
  apply nodeValid_prime [2, 223, 10781] ⟨4808327, 5, [(2, 1), (223, 1), (10781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_223
    · exact prime_10781
  · decide +kernel

theorem prime_5213057 : Nat.Prime 5213057 := by
  apply nodeValid_prime [2, 139, 293] ⟨5213057, 3, [(2, 7), (139, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_293
  · decide +kernel

theorem prime_5369251 : Nat.Prime 5369251 := by
  apply nodeValid_prime [2, 3, 5, 7159] ⟨5369251, 2, [(2, 1), (3, 1), (5, 3), (7159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7159
  · decide +kernel

theorem prime_6567023 : Nat.Prime 6567023 := by
  apply nodeValid_prime [2, 7, 11, 42643] ⟨6567023, 5, [(2, 1), (7, 1), (11, 1), (42643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_42643
  · decide +kernel

theorem prime_6676871 : Nat.Prime 6676871 := by
  apply nodeValid_prime [2, 5, 667687] ⟨6676871, 11, [(2, 1), (5, 1), (667687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_667687
  · decide +kernel

theorem prime_6682721 : Nat.Prime 6682721 := by
  apply nodeValid_prime [2, 5, 11, 3797] ⟨6682721, 3, [(2, 5), (5, 1), (11, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3797
  · decide +kernel

theorem prime_6968557 : Nat.Prime 6968557 := by
  apply nodeValid_prime [2, 3, 7, 27653] ⟨6968557, 6, [(2, 2), (3, 2), (7, 1), (27653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_27653
  · decide +kernel

theorem prime_7102387 : Nat.Prime 7102387 := by
  apply nodeValid_prime [2, 3, 394577] ⟨7102387, 2, [(2, 1), (3, 2), (394577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_394577
  · decide +kernel

theorem prime_7104569 : Nat.Prime 7104569 := by
  apply nodeValid_prime [2, 139, 6389] ⟨7104569, 3, [(2, 3), (139, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_6389
  · decide +kernel

theorem prime_10592567 : Nat.Prime 10592567 := by
  apply nodeValid_prime [2, 67, 137, 577] ⟨10592567, 5, [(2, 1), (67, 1), (137, 1), (577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_137
    · exact prime_577
  · decide +kernel

theorem prime_11297621 : Nat.Prime 11297621 := by
  apply nodeValid_prime [2, 5, 564881] ⟨11297621, 2, [(2, 2), (5, 1), (564881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_564881
  · decide +kernel

theorem prime_13152641 : Nat.Prime 13152641 := by
  apply nodeValid_prime [2, 5, 20551] ⟨13152641, 3, [(2, 7), (5, 1), (20551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_20551
  · decide +kernel

theorem prime_17175701 : Nat.Prime 17175701 := by
  apply nodeValid_prime [2, 5, 171757] ⟨17175701, 3, [(2, 2), (5, 2), (171757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_171757
  · decide +kernel

theorem prime_17294663 : Nat.Prime 17294663 := by
  apply nodeValid_prime [2, 7, 11, 112303] ⟨17294663, 5, [(2, 1), (7, 1), (11, 1), (112303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_112303
  · decide +kernel

theorem prime_19690171 : Nat.Prime 19690171 := by
  apply nodeValid_prime [2, 3, 5, 421, 1559] ⟨19690171, 3, [(2, 1), (3, 1), (5, 1), (421, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_421
    · exact prime_1559
  · decide +kernel

theorem prime_19844983 : Nat.Prime 19844983 := by
  apply nodeValid_prime [2, 3, 1049, 1051] ⟨19844983, 3, [(2, 1), (3, 2), (1049, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1049
    · exact prime_1051
  · decide +kernel

theorem prime_24580891 : Nat.Prime 24580891 := by
  apply nodeValid_prime [2, 3, 5, 113, 2417] ⟨24580891, 2, [(2, 1), (3, 2), (5, 1), (113, 1), (2417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
    · exact prime_2417
  · decide +kernel

theorem prime_29820517 : Nat.Prime 29820517 := by
  apply nodeValid_prime [2, 3, 11, 17, 97, 137] ⟨29820517, 22, [(2, 2), (3, 1), (11, 1), (17, 1), (97, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_97
    · exact prime_137
  · decide +kernel

theorem prime_34006303 : Nat.Prime 34006303 := by
  apply nodeValid_prime [2, 3, 11, 41, 59, 71] ⟨34006303, 6, [(2, 1), (3, 2), (11, 1), (41, 1), (59, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_59
    · exact prime_71
  · decide +kernel

theorem prime_34628897 : Nat.Prime 34628897 := by
  apply nodeValid_prime [2, 1082153] ⟨34628897, 3, [(2, 5), (1082153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1082153
  · decide +kernel

theorem prime_46703693 : Nat.Prime 46703693 := by
  apply nodeValid_prime [2, 7, 17, 59, 1663] ⟨46703693, 2, [(2, 2), (7, 1), (17, 1), (59, 1), (1663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_59
    · exact prime_1663
  · decide +kernel

theorem prime_49971913 : Nat.Prime 49971913 := by
  apply nodeValid_prime [2, 3, 2082163] ⟨49971913, 5, [(2, 3), (3, 1), (2082163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2082163
  · decide +kernel

theorem prime_51389399 : Nat.Prime 51389399 := by
  apply nodeValid_prime [2, 4969, 5171] ⟨51389399, 17, [(2, 1), (4969, 1), (5171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4969
    · exact prime_5171
  · decide +kernel

theorem prime_53162839 : Nat.Prime 53162839 := by
  apply nodeValid_prime [2, 3, 984497] ⟨53162839, 6, [(2, 1), (3, 3), (984497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_984497
  · decide +kernel

theorem prime_87290663 : Nat.Prime 87290663 := by
  apply nodeValid_prime [2, 709, 61559] ⟨87290663, 5, [(2, 1), (709, 1), (61559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_709
    · exact prime_61559
  · decide +kernel

theorem prime_101065787 : Nat.Prime 101065787 := by
  apply nodeValid_prime [2, 2729, 18517] ⟨101065787, 2, [(2, 1), (2729, 1), (18517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2729
    · exact prime_18517
  · decide +kernel

theorem prime_118141027 : Nat.Prime 118141027 := by
  apply nodeValid_prime [2, 3, 19690171] ⟨118141027, 2, [(2, 1), (3, 1), (19690171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19690171
  · decide +kernel

theorem prime_136025213 : Nat.Prime 136025213 := by
  apply nodeValid_prime [2, 34006303] ⟨136025213, 2, [(2, 2), (34006303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34006303
  · decide +kernel

theorem prime_147485347 : Nat.Prime 147485347 := by
  apply nodeValid_prime [2, 3, 24580891] ⟨147485347, 3, [(2, 1), (3, 1), (24580891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24580891
  · decide +kernel

theorem prime_163109981 : Nat.Prime 163109981 := by
  apply nodeValid_prime [2, 5, 11, 741409] ⟨163109981, 3, [(2, 2), (5, 1), (11, 1), (741409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_741409
  · decide +kernel

theorem prime_187670033 : Nat.Prime 187670033 := by
  apply nodeValid_prime [2, 11, 31, 53, 59] ⟨187670033, 3, [(2, 4), (11, 2), (31, 1), (53, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_53
    · exact prime_59
  · decide +kernel

theorem prime_325827107 : Nat.Prime 325827107 := by
  apply nodeValid_prime [2, 11, 37, 36389] ⟨325827107, 5, [(2, 1), (11, 2), (37, 1), (36389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_36389
  · decide +kernel

theorem prime_375340067 : Nat.Prime 375340067 := by
  apply nodeValid_prime [2, 187670033] ⟨375340067, 2, [(2, 1), (187670033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_187670033
  · decide +kernel

theorem prime_519638939 : Nat.Prime 519638939 := by
  apply nodeValid_prime [2, 7, 13, 2855159] ⟨519638939, 2, [(2, 1), (7, 1), (13, 1), (2855159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_2855159
  · decide +kernel

theorem prime_603923483 : Nat.Prime 603923483 := by
  apply nodeValid_prime [2, 8233, 36677] ⟨603923483, 2, [(2, 1), (8233, 1), (36677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8233
    · exact prime_36677
  · decide +kernel

theorem prime_1711324759 : Nat.Prime 1711324759 := by
  apply nodeValid_prime [2, 3, 11, 13, 153427] ⟨1711324759, 6, [(2, 1), (3, 1), (11, 1), (13, 2), (153427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_153427
  · decide +kernel

theorem prime_2856242717 : Nat.Prime 2856242717 := by
  apply nodeValid_prime [2, 19, 53, 709097] ⟨2856242717, 2, [(2, 2), (19, 1), (53, 1), (709097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_53
    · exact prime_709097
  · decide +kernel

theorem prime_2904087119 : Nat.Prime 2904087119 := by
  apply nodeValid_prime [2, 17, 113, 755879] ⟨2904087119, 13, [(2, 1), (17, 1), (113, 1), (755879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_113
    · exact prime_755879
  · decide +kernel

theorem prime_5239739191 : Nat.Prime 5239739191 := by
  apply nodeValid_prime [2, 3, 5, 7, 1231, 20269] ⟨5239739191, 13, [(2, 1), (3, 1), (5, 1), (7, 1), (1231, 1), (20269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1231
    · exact prime_20269
  · decide +kernel

theorem prime_12609997111 : Nat.Prime 12609997111 := by
  apply nodeValid_prime [2, 3, 5, 46703693] ⟨12609997111, 19, [(2, 1), (3, 3), (5, 1), (46703693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_46703693
  · decide +kernel

theorem prime_19325551457 : Nat.Prime 19325551457 := by
  apply nodeValid_prime [2, 603923483] ⟨19325551457, 3, [(2, 5), (603923483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_603923483
  · decide +kernel

theorem prime_76935215939 : Nat.Prime 76935215939 := by
  apply nodeValid_prime [2, 7, 65327, 84121] ⟨76935215939, 2, [(2, 1), (7, 1), (65327, 1), (84121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_65327
    · exact prime_84121
  · decide +kernel

theorem prime_149515922201 : Nat.Prime 149515922201 := by
  apply nodeValid_prime [2, 5, 479, 1560709] ⟨149515922201, 6, [(2, 3), (5, 2), (479, 1), (1560709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_479
    · exact prime_1560709
  · decide +kernel

theorem prime_149515962961 : Nat.Prime 149515962961 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 61, 89, 97] ⟨149515962961, 22, [(2, 4), (3, 1), (5, 1), (7, 1), (13, 2), (61, 1), (89, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_61
    · exact prime_89
    · exact prime_97
  · decide +kernel

theorem prime_149515963697 : Nat.Prime 149515963697 := by
  apply nodeValid_prime [2, 11, 17, 49971913] ⟨149515963697, 3, [(2, 4), (11, 1), (17, 1), (49971913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_49971913
  · decide +kernel

theorem prime_149875549559 : Nat.Prime 149875549559 := by
  apply nodeValid_prime [2, 7, 619, 17294663] ⟨149875549559, 7, [(2, 1), (7, 1), (619, 1), (17294663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_619
    · exact prime_17294663
  · decide +kernel

theorem prime_149875552591 : Nat.Prime 149875552591 := by
  apply nodeValid_prime [2, 3, 5, 1039, 4808327] ⟨149875552591, 3, [(2, 1), (3, 1), (5, 1), (1039, 1), (4808327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1039
    · exact prime_4808327
  · decide +kernel

theorem prime_149875553923 : Nat.Prime 149875553923 := by
  apply nodeValid_prime [2, 3, 67, 613, 739, 823] ⟨149875553923, 5, [(2, 1), (3, 1), (67, 1), (613, 1), (739, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_613
    · exact prime_739
    · exact prime_823
  · decide +kernel

theorem prime_150235764059 : Nat.Prime 150235764059 := by
  apply nodeValid_prime [2, 61, 109, 11297621] ⟨150235764059, 2, [(2, 1), (61, 1), (109, 1), (11297621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_109
    · exact prime_11297621
  · decide +kernel

theorem prime_150235764647 : Nat.Prime 150235764647 := by
  apply nodeValid_prime [2, 11, 229, 29820517] ⟨150235764647, 5, [(2, 1), (11, 1), (229, 1), (29820517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_229
    · exact prime_29820517
  · decide +kernel

theorem prime_150235767443 : Nat.Prime 150235767443 := by
  apply nodeValid_prime [2, 50341, 1492181] ⟨150235767443, 2, [(2, 1), (50341, 1), (1492181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_50341
    · exact prime_1492181
  · decide +kernel

theorem prime_150596546357 : Nat.Prime 150596546357 := by
  apply nodeValid_prime [2, 13291, 2832679] ⟨150596546357, 2, [(2, 2), (13291, 1), (2832679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13291
    · exact prime_2832679
  · decide +kernel

theorem prime_150596546369 : Nat.Prime 150596546369 := by
  apply nodeValid_prime [2, 137, 17175701] ⟨150596546369, 3, [(2, 6), (137, 1), (17175701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_17175701
  · decide +kernel

theorem prime_150596578793 : Nat.Prime 150596578793 := by
  apply nodeValid_prime [2, 11, 1711324759] ⟨150596578793, 3, [(2, 3), (11, 1), (1711324759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1711324759
  · decide +kernel

theorem prime_150957969557 : Nat.Prime 150957969557 := by
  apply nodeValid_prime [2, 9173, 4114193] ⟨150957969557, 2, [(2, 2), (9173, 1), (4114193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9173
    · exact prime_4114193
  · decide +kernel

theorem prime_150957969611 : Nat.Prime 150957969611 := by
  apply nodeValid_prime [2, 5, 7, 127, 157, 15451] ⟨150957969611, 2, [(2, 1), (5, 1), (7, 2), (127, 1), (157, 1), (15451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_127
    · exact prime_157
    · exact prime_15451
  · decide +kernel

theorem prime_150957982519 : Nat.Prime 150957982519 := by
  apply nodeValid_prime [2, 3, 7, 9371, 383549] ⟨150957982519, 3, [(2, 1), (3, 1), (7, 1), (9371, 1), (383549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9371
    · exact prime_383549
  · decide +kernel

theorem prime_151319965333 : Nat.Prime 151319965333 := by
  apply nodeValid_prime [2, 3, 12609997111] ⟨151319965333, 2, [(2, 2), (3, 1), (12609997111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12609997111
  · decide +kernel

theorem prime_151319966023 : Nat.Prime 151319966023 := by
  apply nodeValid_prime [2, 3, 19, 147485347] ⟨151319966023, 5, [(2, 1), (3, 3), (19, 1), (147485347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_147485347
  · decide +kernel

theorem prime_151319973001 : Nat.Prime 151319973001 := by
  apply nodeValid_prime [2, 3, 5, 7, 37, 194749] ⟨151319973001, 29, [(2, 3), (3, 1), (5, 3), (7, 1), (37, 1), (194749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_37
    · exact prime_194749
  · decide +kernel

theorem prime_151682548151 : Nat.Prime 151682548151 := by
  apply nodeValid_prime [2, 5, 7, 61, 7104569] ⟨151682548151, 7, [(2, 1), (5, 2), (7, 1), (61, 1), (7104569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_7104569
  · decide +kernel

theorem prime_151682548189 : Nat.Prime 151682548189 := by
  apply nodeValid_prime [2, 3, 18583, 680203] ⟨151682548189, 14, [(2, 2), (3, 1), (18583, 1), (680203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_18583
    · exact prime_680203
  · decide +kernel

theorem prime_151682551907 : Nat.Prime 151682551907 := by
  apply nodeValid_prime [2, 547, 4583, 30253] ⟨151682551907, 2, [(2, 1), (547, 1), (4583, 1), (30253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_547
    · exact prime_4583
    · exact prime_30253
  · decide +kernel

theorem prime_152045706413 : Nat.Prime 152045706413 := by
  apply nodeValid_prime [2, 5693, 6676871] ⟨152045706413, 2, [(2, 2), (5693, 1), (6676871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5693
    · exact prime_6676871
  · decide +kernel

theorem prime_152045706719 : Nat.Prime 152045706719 := by
  apply nodeValid_prime [2, 7177, 10592567] ⟨152045706719, 7, [(2, 1), (7177, 1), (10592567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7177
    · exact prime_10592567
  · decide +kernel

theorem prime_152045719541 : Nat.Prime 152045719541 := by
  apply nodeValid_prime [2, 5, 11, 13, 53162839] ⟨152045719541, 14, [(2, 2), (5, 1), (11, 1), (13, 1), (53162839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_53162839
  · decide +kernel

theorem prime_152409469441 : Nat.Prime 152409469441 := by
  apply nodeValid_prime [2, 3, 5, 19844983] ⟨152409469441, 7, [(2, 9), (3, 1), (5, 1), (19844983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19844983
  · decide +kernel

theorem prime_152409497599 : Nat.Prime 152409497599 := by
  apply nodeValid_prime [2, 3, 97, 87290663] ⟨152409497599, 6, [(2, 1), (3, 2), (97, 1), (87290663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_87290663
  · decide +kernel

theorem prime_152409498739 : Nat.Prime 152409498739 := by
  apply nodeValid_prime [2, 3, 7, 101, 109, 113, 2917] ⟨152409498739, 2, [(2, 1), (3, 1), (7, 1), (101, 1), (109, 1), (113, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
    · exact prime_109
    · exact prime_113
    · exact prime_2917
  · decide +kernel

theorem prime_152773807103 : Nat.Prime 152773807103 := by
  apply nodeValid_prime [2, 7, 71, 3637, 6037] ⟨152773807103, 5, [(2, 1), (7, 2), (71, 1), (3637, 1), (6037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71
    · exact prime_3637
    · exact prime_6037
  · decide +kernel

theorem prime_152773848067 : Nat.Prime 152773848067 := by
  apply nodeValid_prime [2, 3, 7, 519638939] ⟨152773848067, 2, [(2, 1), (3, 1), (7, 2), (519638939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_519638939
  · decide +kernel

theorem prime_152773848443 : Nat.Prime 152773848443 := by
  apply nodeValid_prime [2, 14653, 5213057] ⟨152773848443, 2, [(2, 1), (14653, 1), (5213057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_14653
    · exact prime_5213057
  · decide +kernel

theorem prime_153138740291 : Nat.Prime 153138740291 := by
  apply nodeValid_prime [2, 5, 47, 325827107] ⟨153138740291, 2, [(2, 1), (5, 1), (47, 1), (325827107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_325827107
  · decide +kernel

theorem prime_153138741319 : Nat.Prime 153138741319 := by
  apply nodeValid_prime [2, 3, 17, 1013, 164677] ⟨153138741319, 3, [(2, 1), (3, 3), (17, 1), (1013, 1), (164677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1013
    · exact prime_164677
  · decide +kernel

theorem prime_153138747337 : Nat.Prime 153138747337 := by
  apply nodeValid_prime [2, 3, 17, 375340067] ⟨153138747337, 5, [(2, 3), (3, 1), (17, 1), (375340067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_375340067
  · decide +kernel

theorem prime_153504266561 : Nat.Prime 153504266561 := by
  apply nodeValid_prime [2, 5, 89, 1523, 3539] ⟨153504266561, 3, [(2, 6), (5, 1), (89, 1), (1523, 1), (3539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_1523
    · exact prime_3539
  · decide +kernel

theorem prime_153504282427 : Nat.Prime 153504282427 := by
  apply nodeValid_prime [2, 3, 11, 31, 631, 118901] ⟨153504282427, 2, [(2, 1), (3, 1), (11, 1), (31, 1), (631, 1), (118901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_631
    · exact prime_118901
  · decide +kernel

theorem prime_153504282937 : Nat.Prime 153504282937 := by
  apply nodeValid_prime [2, 3, 83, 89, 865847] ⟨153504282937, 5, [(2, 3), (3, 1), (83, 1), (89, 1), (865847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_89
    · exact prime_865847
  · decide +kernel

theorem prime_153870390503 : Nat.Prime 153870390503 := by
  apply nodeValid_prime [2, 58693, 1310807] ⟨153870390503, 5, [(2, 1), (58693, 1), (1310807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_58693
    · exact prime_1310807
  · decide +kernel

theorem prime_153870430729 : Nat.Prime 153870430729 := by
  apply nodeValid_prime [2, 3, 7, 479, 273157] ⟨153870430729, 13, [(2, 3), (3, 1), (7, 2), (479, 1), (273157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_479
    · exact prime_273157
  · decide +kernel

theorem prime_153870431879 : Nat.Prime 153870431879 := by
  apply nodeValid_prime [2, 76935215939] ⟨153870431879, 13, [(2, 1), (76935215939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_76935215939
  · decide +kernel

theorem prime_154237104227 : Nat.Prime 154237104227 := by
  apply nodeValid_prime [2, 53, 271, 5369251] ⟨154237104227, 2, [(2, 1), (53, 1), (271, 1), (5369251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_271
    · exact prime_5369251
  · decide +kernel

theorem prime_154237106719 : Nat.Prime 154237106719 := by
  apply nodeValid_prime [2, 3, 2856242717] ⟨154237106719, 3, [(2, 1), (3, 3), (2856242717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2856242717
  · decide +kernel

theorem prime_154237107239 : Nat.Prime 154237107239 := by
  apply nodeValid_prime [2, 17, 131, 34628897] ⟨154237107239, 19, [(2, 1), (17, 1), (131, 1), (34628897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_131
    · exact prime_34628897
  · decide +kernel

theorem prime_154604405603 : Nat.Prime 154604405603 := by
  apply nodeValid_prime [2, 11093, 6968557] ⟨154604405603, 2, [(2, 1), (11093, 1), (6968557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11093
    · exact prime_6968557
  · decide +kernel

theorem prime_154604411369 : Nat.Prime 154604411369 := by
  apply nodeValid_prime [2, 11, 59, 2707039] ⟨154604411369, 3, [(2, 3), (11, 2), (59, 1), (2707039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_2707039
  · decide +kernel

theorem prime_154604411657 : Nat.Prime 154604411657 := by
  apply nodeValid_prime [2, 19325551457] ⟨154604411657, 3, [(2, 3), (19325551457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19325551457
  · decide +kernel

theorem prime_154972299023 : Nat.Prime 154972299023 := by
  apply nodeValid_prime [2, 43, 887, 2031571] ⟨154972299023, 5, [(2, 1), (43, 1), (887, 1), (2031571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_887
    · exact prime_2031571
  · decide +kernel

theorem prime_154972299991 : Nat.Prime 154972299991 := by
  apply nodeValid_prime [2, 3, 5, 773, 6682721] ⟨154972299991, 3, [(2, 1), (3, 1), (5, 1), (773, 1), (6682721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_773
    · exact prime_6682721
  · decide +kernel

theorem prime_154972302559 : Nat.Prime 154972302559 := by
  apply nodeValid_prime [2, 3, 29, 21401, 41617] ⟨154972302559, 3, [(2, 1), (3, 1), (29, 1), (21401, 1), (41617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_21401
    · exact prime_41617
  · decide +kernel

theorem prime_155340793247 : Nat.Prime 155340793247 := by
  apply nodeValid_prime [2, 571, 136025213] ⟨155340793247, 5, [(2, 1), (571, 1), (136025213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_571
    · exact prime_136025213
  · decide +kernel

theorem prime_155340794767 : Nat.Prime 155340794767 := by
  apply nodeValid_prime [2, 3, 61, 283, 751, 1997] ⟨155340794767, 5, [(2, 1), (3, 1), (61, 1), (283, 1), (751, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_283
    · exact prime_751
    · exact prime_1997
  · decide +kernel

theorem prime_155340794951 : Nat.Prime 155340794951 := by
  apply nodeValid_prime [2, 5, 11, 3181, 88789] ⟨155340794951, 11, [(2, 1), (5, 2), (11, 1), (3181, 1), (88789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_3181
    · exact prime_88789
  · decide +kernel

theorem prime_155709873587 : Nat.Prime 155709873587 := by
  apply nodeValid_prime [2, 659, 118141027] ⟨155709873587, 2, [(2, 1), (659, 1), (118141027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_659
    · exact prime_118141027
  · decide +kernel

theorem prime_155709873817 : Nat.Prime 155709873817 := by
  apply nodeValid_prime [2, 3, 7, 37, 89, 7607] ⟨155709873817, 5, [(2, 3), (3, 1), (7, 1), (37, 2), (89, 1), (7607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_89
    · exact prime_7607
  · decide +kernel

theorem prime_155709878971 : Nat.Prime 155709878971 := by
  apply nodeValid_prime [2, 3, 5, 101, 51389399] ⟨155709878971, 3, [(2, 1), (3, 1), (5, 1), (101, 1), (51389399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_51389399
  · decide +kernel

theorem prime_156079557301 : Nat.Prime 156079557301 := by
  apply nodeValid_prime [2, 3, 5, 29, 727, 24677] ⟨156079557301, 6, [(2, 2), (3, 1), (5, 2), (29, 1), (727, 1), (24677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_727
    · exact prime_24677
  · decide +kernel

theorem prime_156079578211 : Nat.Prime 156079578211 := by
  apply nodeValid_prime [2, 3, 5, 61, 1373, 62119] ⟨156079578211, 2, [(2, 1), (3, 1), (5, 1), (61, 1), (1373, 1), (62119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_1373
    · exact prime_62119
  · decide +kernel

theorem prime_156079578299 : Nat.Prime 156079578299 := by
  apply nodeValid_prime [2, 7, 10247, 1087981] ⟨156079578299, 2, [(2, 1), (7, 1), (10247, 1), (1087981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_10247
    · exact prime_1087981
  · decide +kernel

theorem prime_156449829733 : Nat.Prime 156449829733 := by
  apply nodeValid_prime [2, 3, 7, 433, 614483] ⟨156449829733, 13, [(2, 2), (3, 1), (7, 2), (433, 1), (614483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_433
    · exact prime_614483
  · decide +kernel

theorem prime_156449837239 : Nat.Prime 156449837239 := by
  apply nodeValid_prime [2, 3, 144563, 180371] ⟨156449837239, 3, [(2, 1), (3, 1), (144563, 1), (180371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_144563
    · exact prime_180371
  · decide +kernel

theorem prime_156449838277 : Nat.Prime 156449838277 := by
  apply nodeValid_prime [2, 3, 43, 101065787] ⟨156449838277, 6, [(2, 2), (3, 2), (43, 1), (101065787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_101065787
  · decide +kernel

theorem prime_156820701997 : Nat.Prime 156820701997 := by
  apply nodeValid_prime [2, 3, 7, 97, 2138503] ⟨156820701997, 2, [(2, 2), (3, 3), (7, 1), (97, 1), (2138503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_97
    · exact prime_2138503
  · decide +kernel

theorem prime_156820704427 : Nat.Prime 156820704427 := by
  apply nodeValid_prime [2, 3, 2904087119] ⟨156820704427, 2, [(2, 1), (3, 3), (2904087119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2904087119
  · decide +kernel

theorem prime_156820704961 : Nat.Prime 156820704961 := by
  apply nodeValid_prime [2, 3, 5, 23, 7102387] ⟨156820704961, 11, [(2, 6), (3, 1), (5, 1), (23, 1), (7102387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_7102387
  · decide +kernel

theorem prime_157192175731 : Nat.Prime 157192175731 := by
  apply nodeValid_prime [2, 3, 5, 5239739191] ⟨157192175731, 2, [(2, 1), (3, 1), (5, 1), (5239739191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5239739191
  · decide +kernel

theorem prime_157192180511 : Nat.Prime 157192180511 := by
  apply nodeValid_prime [2, 5, 4481, 3507971] ⟨157192180511, 7, [(2, 1), (5, 1), (4481, 1), (3507971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4481
    · exact prime_3507971
  · decide +kernel

theorem prime_157192181261 : Nat.Prime 157192181261 := by
  apply nodeValid_prime [2, 5, 5479, 1434497] ⟨157192181261, 2, [(2, 2), (5, 1), (5479, 1), (1434497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5479
    · exact prime_1434497
  · decide +kernel

theorem prime_157564180843 : Nat.Prime 157564180843 := by
  apply nodeValid_prime [2, 3, 17, 2633, 34511] ⟨157564180843, 3, [(2, 1), (3, 1), (17, 2), (2633, 1), (34511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2633
    · exact prime_34511
  · decide +kernel

theorem prime_157564181069 : Nat.Prime 157564181069 := by
  apply nodeValid_prime [2, 7, 2671, 300973] ⟨157564181069, 2, [(2, 2), (7, 2), (2671, 1), (300973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2671
    · exact prime_300973
  · decide +kernel

theorem prime_157564241647 : Nat.Prime 157564241647 := by
  apply nodeValid_prime [2, 3, 7, 23, 163109981] ⟨157564241647, 7, [(2, 1), (3, 1), (7, 1), (23, 1), (163109981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_163109981
  · decide +kernel

theorem prime_157936903151 : Nat.Prime 157936903151 := by
  apply nodeValid_prime [2, 5, 13, 37, 6567023] ⟨157936903151, 11, [(2, 1), (5, 2), (13, 1), (37, 1), (6567023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_37
    · exact prime_6567023
  · decide +kernel

theorem prime_157936913129 : Nat.Prime 157936913129 := by
  apply nodeValid_prime [2, 19, 79, 13152641] ⟨157936913129, 3, [(2, 3), (19, 1), (79, 1), (13152641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_79
    · exact prime_13152641
  · decide +kernel

theorem prime_157936913401 : Nat.Prime 157936913401 := by
  apply nodeValid_prime [2, 3, 5, 7, 113, 332779] ⟨157936913401, 29, [(2, 3), (3, 1), (5, 2), (7, 1), (113, 1), (332779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_113
    · exact prime_332779
  · decide +kernel

theorem prime_158310162209 : Nat.Prime 158310162209 := by
  apply nodeValid_prime [2, 11, 229, 16231] ⟨158310162209, 3, [(2, 5), (11, 3), (229, 1), (16231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_229
    · exact prime_16231
  · decide +kernel

theorem prime_158310163079 : Nat.Prime 158310163079 := by
  apply nodeValid_prime [2, 17, 4493, 1036319] ⟨158310163079, 19, [(2, 1), (17, 1), (4493, 1), (1036319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4493
    · exact prime_1036319
  · decide +kernel

theorem prime_158310163369 : Nat.Prime 158310163369 := by
  apply nodeValid_prime [2, 3, 7, 37, 76481] ⟨158310163369, 13, [(2, 3), (3, 3), (7, 1), (37, 2), (76481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_76481
  · decide +kernel

end Sude.Lucas.Generated
