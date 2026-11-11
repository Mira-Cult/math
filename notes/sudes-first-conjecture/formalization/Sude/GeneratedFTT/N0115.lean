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
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0093
import Sude.GeneratedFTT.N0094
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0111
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0113

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_3709 : Nat.Prime 3709 := by
  apply nodeValid_prime [2, 3, 103] ⟨3709, 2, [(2, 2), (3, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_15559 : Nat.Prime 15559 := by
  apply nodeValid_prime [2, 3, 2593] ⟨15559, 3, [(2, 1), (3, 1), (2593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2593
  · decide +kernel

theorem prime_16981 : Nat.Prime 16981 := by
  apply nodeValid_prime [2, 3, 5, 283] ⟨16981, 2, [(2, 2), (3, 1), (5, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_283
  · decide +kernel

theorem prime_23209 : Nat.Prime 23209 := by
  apply nodeValid_prime [2, 3, 967] ⟨23209, 31, [(2, 3), (3, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_967
  · decide +kernel

theorem prime_27427 : Nat.Prime 27427 := by
  apply nodeValid_prime [2, 3, 7, 653] ⟨27427, 5, [(2, 1), (3, 1), (7, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_653
  · decide +kernel

theorem prime_28627 : Nat.Prime 28627 := by
  apply nodeValid_prime [2, 3, 13, 367] ⟨28627, 5, [(2, 1), (3, 1), (13, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_367
  · decide +kernel

theorem prime_39133 : Nat.Prime 39133 := by
  apply nodeValid_prime [2, 3, 1087] ⟨39133, 5, [(2, 2), (3, 2), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1087
  · decide +kernel

theorem prime_39323 : Nat.Prime 39323 := by
  apply nodeValid_prime [2, 19661] ⟨39323, 2, [(2, 1), (19661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19661
  · decide +kernel

theorem prime_41399 : Nat.Prime 41399 := by
  apply nodeValid_prime [2, 7, 2957] ⟨41399, 7, [(2, 1), (7, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2957
  · decide +kernel

theorem prime_43049 : Nat.Prime 43049 := by
  apply nodeValid_prime [2, 5381] ⟨43049, 3, [(2, 3), (5381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5381
  · decide +kernel

theorem prime_43451 : Nat.Prime 43451 := by
  apply nodeValid_prime [2, 5, 11, 79] ⟨43451, 2, [(2, 1), (5, 2), (11, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_79
  · decide +kernel

theorem prime_45131 : Nat.Prime 45131 := by
  apply nodeValid_prime [2, 5, 4513] ⟨45131, 2, [(2, 1), (5, 1), (4513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4513
  · decide +kernel

theorem prime_65617 : Nat.Prime 65617 := by
  apply nodeValid_prime [2, 3, 1367] ⟨65617, 13, [(2, 4), (3, 1), (1367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1367
  · decide +kernel

theorem prime_67141 : Nat.Prime 67141 := by
  apply nodeValid_prime [2, 3, 5, 373] ⟨67141, 2, [(2, 2), (3, 2), (5, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_373
  · decide +kernel

theorem prime_70729 : Nat.Prime 70729 := by
  apply nodeValid_prime [2, 3, 7, 421] ⟨70729, 22, [(2, 3), (3, 1), (7, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_421
  · decide +kernel

theorem prime_71191 : Nat.Prime 71191 := by
  apply nodeValid_prime [2, 3, 5, 7, 113] ⟨71191, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_73237 : Nat.Prime 73237 := by
  apply nodeValid_prime [2, 3, 17, 359] ⟨73237, 6, [(2, 2), (3, 1), (17, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_359
  · decide +kernel

theorem prime_77647 : Nat.Prime 77647 := by
  apply nodeValid_prime [2, 3, 12941] ⟨77647, 3, [(2, 1), (3, 1), (12941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12941
  · decide +kernel

theorem prime_80557 : Nat.Prime 80557 := by
  apply nodeValid_prime [2, 3, 7, 137] ⟨80557, 2, [(2, 2), (3, 1), (7, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_137
  · decide +kernel

theorem prime_82799 : Nat.Prime 82799 := by
  apply nodeValid_prime [2, 41399] ⟨82799, 13, [(2, 1), (41399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41399
  · decide +kernel

theorem prime_119659 : Nat.Prime 119659 := by
  apply nodeValid_prime [2, 3, 7, 11, 37] ⟨119659, 3, [(2, 1), (3, 1), (7, 2), (11, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_37
  · decide +kernel

theorem prime_120661 : Nat.Prime 120661 := by
  apply nodeValid_prime [2, 3, 5, 2011] ⟨120661, 2, [(2, 2), (3, 1), (5, 1), (2011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2011
  · decide +kernel

theorem prime_137587 : Nat.Prime 137587 := by
  apply nodeValid_prime [2, 3, 23, 997] ⟨137587, 3, [(2, 1), (3, 1), (23, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_997
  · decide +kernel

theorem prime_137873 : Nat.Prime 137873 := by
  apply nodeValid_prime [2, 7, 1231] ⟨137873, 3, [(2, 4), (7, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1231
  · decide +kernel

theorem prime_158489 : Nat.Prime 158489 := by
  apply nodeValid_prime [2, 11, 1801] ⟨158489, 3, [(2, 3), (11, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1801
  · decide +kernel

theorem prime_163151 : Nat.Prime 163151 := by
  apply nodeValid_prime [2, 5, 13, 251] ⟨163151, 7, [(2, 1), (5, 2), (13, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_251
  · decide +kernel

theorem prime_168731 : Nat.Prime 168731 := by
  apply nodeValid_prime [2, 5, 47, 359] ⟨168731, 2, [(2, 1), (5, 1), (47, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_359
  · decide +kernel

theorem prime_215123 : Nat.Prime 215123 := by
  apply nodeValid_prime [2, 29, 3709] ⟨215123, 2, [(2, 1), (29, 1), (3709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_3709
  · decide +kernel

theorem prime_228509 : Nat.Prime 228509 := by
  apply nodeValid_prime [2, 7, 8161] ⟨228509, 2, [(2, 2), (7, 1), (8161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_8161
  · decide +kernel

theorem prime_234799 : Nat.Prime 234799 := by
  apply nodeValid_prime [2, 3, 39133] ⟨234799, 3, [(2, 1), (3, 1), (39133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39133
  · decide +kernel

theorem prime_240869 : Nat.Prime 240869 := by
  apply nodeValid_prime [2, 60217] ⟨240869, 2, [(2, 2), (60217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60217
  · decide +kernel

theorem prime_256057 : Nat.Prime 256057 := by
  apply nodeValid_prime [2, 3, 47, 227] ⟨256057, 11, [(2, 3), (3, 1), (47, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_227
  · decide +kernel

theorem prime_257123 : Nat.Prime 257123 := by
  apply nodeValid_prime [2, 59, 2179] ⟨257123, 2, [(2, 1), (59, 1), (2179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_2179
  · decide +kernel

theorem prime_258241 : Nat.Prime 258241 := by
  apply nodeValid_prime [2, 3, 5, 269] ⟨258241, 17, [(2, 6), (3, 1), (5, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_269
  · decide +kernel

theorem prime_280463 : Nat.Prime 280463 := by
  apply nodeValid_prime [2, 7, 13, 23, 67] ⟨280463, 5, [(2, 1), (7, 1), (13, 1), (23, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_23
    · exact prime_67
  · decide +kernel

theorem prime_288427 : Nat.Prime 288427 := by
  apply nodeValid_prime [2, 3, 53, 907] ⟨288427, 5, [(2, 1), (3, 1), (53, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_907
  · decide +kernel

theorem prime_327599 : Nat.Prime 327599 := by
  apply nodeValid_prime [2, 19, 37, 233] ⟨327599, 19, [(2, 1), (19, 1), (37, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_233
  · decide +kernel

theorem prime_335771 : Nat.Prime 335771 := by
  apply nodeValid_prime [2, 5, 33577] ⟨335771, 6, [(2, 1), (5, 1), (33577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_33577
  · decide +kernel

theorem prime_356261 : Nat.Prime 356261 := by
  apply nodeValid_prime [2, 5, 47, 379] ⟨356261, 2, [(2, 2), (5, 1), (47, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_47
    · exact prime_379
  · decide +kernel

theorem prime_424693 : Nat.Prime 424693 := by
  apply nodeValid_prime [2, 3, 47, 251] ⟨424693, 2, [(2, 2), (3, 2), (47, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_251
  · decide +kernel

theorem prime_514247 : Nat.Prime 514247 := by
  apply nodeValid_prime [2, 257123] ⟨514247, 5, [(2, 1), (257123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_257123
  · decide +kernel

theorem prime_529007 : Nat.Prime 529007 := by
  apply nodeValid_prime [2, 17, 15559] ⟨529007, 5, [(2, 1), (17, 1), (15559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_15559
  · decide +kernel

theorem prime_576469 : Nat.Prime 576469 := by
  apply nodeValid_prime [2, 3, 67, 239] ⟨576469, 6, [(2, 2), (3, 2), (67, 1), (239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_239
  · decide +kernel

theorem prime_649081 : Nat.Prime 649081 := by
  apply nodeValid_prime [2, 3, 5, 601] ⟨649081, 19, [(2, 3), (3, 3), (5, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_601
  · decide +kernel

theorem prime_682289 : Nat.Prime 682289 := by
  apply nodeValid_prime [2, 42643] ⟨682289, 3, [(2, 4), (42643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42643
  · decide +kernel

theorem prime_805061 : Nat.Prime 805061 := by
  apply nodeValid_prime [2, 5, 40253] ⟨805061, 2, [(2, 2), (5, 1), (40253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40253
  · decide +kernel

theorem prime_883013 : Nat.Prime 883013 := by
  apply nodeValid_prime [2, 13, 16981] ⟨883013, 2, [(2, 2), (13, 1), (16981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_16981
  · decide +kernel

theorem prime_1008607 : Nat.Prime 1008607 := by
  apply nodeValid_prime [2, 3, 97, 1733] ⟨1008607, 3, [(2, 1), (3, 1), (97, 1), (1733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_1733
  · decide +kernel

theorem prime_1095839 : Nat.Prime 1095839 := by
  apply nodeValid_prime [2, 179, 3061] ⟨1095839, 23, [(2, 1), (179, 1), (3061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_3061
  · decide +kernel

theorem prime_1281439 : Nat.Prime 1281439 := by
  apply nodeValid_prime [2, 3, 71191] ⟨1281439, 3, [(2, 1), (3, 2), (71191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71191
  · decide +kernel

theorem prime_1318267 : Nat.Prime 1318267 := by
  apply nodeValid_prime [2, 3, 73237] ⟨1318267, 2, [(2, 1), (3, 2), (73237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73237
  · decide +kernel

theorem prime_1536343 : Nat.Prime 1536343 := by
  apply nodeValid_prime [2, 3, 256057] ⟨1536343, 5, [(2, 1), (3, 1), (256057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_256057
  · decide +kernel

theorem prime_1610123 : Nat.Prime 1610123 := by
  apply nodeValid_prime [2, 805061] ⟨1610123, 2, [(2, 1), (805061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_805061
  · decide +kernel

theorem prime_1655981 : Nat.Prime 1655981 := by
  apply nodeValid_prime [2, 5, 82799] ⟨1655981, 2, [(2, 2), (5, 1), (82799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_82799
  · decide +kernel

theorem prime_1698773 : Nat.Prime 1698773 := by
  apply nodeValid_prime [2, 424693] ⟨1698773, 2, [(2, 2), (424693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_424693
  · decide +kernel

theorem prime_1779299 : Nat.Prime 1779299 := by
  apply nodeValid_prime [2, 113, 7873] ⟨1779299, 2, [(2, 1), (113, 1), (7873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_7873
  · decide +kernel

theorem prime_1818307 : Nat.Prime 1818307 := by
  apply nodeValid_prime [2, 3, 7, 14431] ⟨1818307, 3, [(2, 1), (3, 2), (7, 1), (14431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14431
  · decide +kernel

theorem prime_2083553 : Nat.Prime 2083553 := by
  apply nodeValid_prime [2, 65111] ⟨2083553, 3, [(2, 5), (65111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_65111
  · decide +kernel

theorem prime_2149127 : Nat.Prime 2149127 := by
  apply nodeValid_prime [2, 7, 153509] ⟨2149127, 5, [(2, 1), (7, 1), (153509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_153509
  · decide +kernel

theorem prime_2625433 : Nat.Prime 2625433 := by
  apply nodeValid_prime [2, 3, 139, 787] ⟨2625433, 5, [(2, 3), (3, 1), (139, 1), (787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_787
  · decide +kernel

theorem prime_2881159 : Nat.Prime 2881159 := by
  apply nodeValid_prime [2, 3, 7, 181, 379] ⟨2881159, 6, [(2, 1), (3, 1), (7, 1), (181, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_181
    · exact prime_379
  · decide +kernel

theorem prime_2890429 : Nat.Prime 2890429 := by
  apply nodeValid_prime [2, 3, 240869] ⟨2890429, 2, [(2, 2), (3, 1), (240869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_240869
  · decide +kernel

theorem prime_3439427 : Nat.Prime 3439427 := by
  apply nodeValid_prime [2, 97, 17729] ⟨3439427, 2, [(2, 1), (97, 1), (17729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_17729
  · decide +kernel

theorem prime_5399393 : Nat.Prime 5399393 := by
  apply nodeValid_prime [2, 168731] ⟨5399393, 3, [(2, 5), (168731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_168731
  · decide +kernel

theorem prime_5510311 : Nat.Prime 5510311 := by
  apply nodeValid_prime [2, 3, 5, 13, 71, 199] ⟨5510311, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (71, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_71
    · exact prime_199
  · decide +kernel

theorem prime_6138689 : Nat.Prime 6138689 := by
  apply nodeValid_prime [2, 95917] ⟨6138689, 3, [(2, 6), (95917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_95917
  · decide +kernel

theorem prime_6225677 : Nat.Prime 6225677 := by
  apply nodeValid_prime [2, 181, 8599] ⟨6225677, 2, [(2, 2), (181, 1), (8599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_8599
  · decide +kernel

theorem prime_6913661 : Nat.Prime 6913661 := by
  apply nodeValid_prime [2, 5, 13, 26591] ⟨6913661, 2, [(2, 2), (5, 1), (13, 1), (26591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_26591
  · decide +kernel

theorem prime_7176121 : Nat.Prime 7176121 := by
  apply nodeValid_prime [2, 3, 5, 7, 8543] ⟨7176121, 37, [(2, 3), (3, 1), (5, 1), (7, 1), (8543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_8543
  · decide +kernel

theorem prime_7862377 : Nat.Prime 7862377 := by
  apply nodeValid_prime [2, 3, 327599] ⟨7862377, 5, [(2, 3), (3, 1), (327599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_327599
  · decide +kernel

theorem prime_9051257 : Nat.Prime 9051257 := by
  apply nodeValid_prime [2, 31, 36497] ⟨9051257, 3, [(2, 3), (31, 1), (36497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_36497
  · decide +kernel

theorem prime_9790987 : Nat.Prime 9790987 := by
  apply nodeValid_prime [2, 3, 97, 16823] ⟨9790987, 2, [(2, 1), (3, 1), (97, 1), (16823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_16823
  · decide +kernel

theorem prime_10682267 : Nat.Prime 10682267 := by
  apply nodeValid_prime [2, 7, 29, 83, 317] ⟨10682267, 2, [(2, 1), (7, 1), (29, 1), (83, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_83
    · exact prime_317
  · decide +kernel

theorem prime_11242373 : Nat.Prime 11242373 := by
  apply nodeValid_prime [2, 17, 29, 5701] ⟨11242373, 2, [(2, 2), (17, 1), (29, 1), (5701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_5701
  · decide +kernel

theorem prime_11526373 : Nat.Prime 11526373 := by
  apply nodeValid_prime [2, 3, 11, 13, 2239] ⟨11526373, 2, [(2, 2), (3, 2), (11, 1), (13, 1), (2239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_2239
  · decide +kernel

theorem prime_13247849 : Nat.Prime 13247849 := by
  apply nodeValid_prime [2, 1655981] ⟨13247849, 3, [(2, 3), (1655981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1655981
  · decide +kernel

theorem prime_15166031 : Nat.Prime 15166031 := by
  apply nodeValid_prime [2, 5, 11, 137873] ⟨15166031, 11, [(2, 1), (5, 1), (11, 1), (137873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_137873
  · decide +kernel

theorem prime_17553997 : Nat.Prime 17553997 := by
  apply nodeValid_prime [2, 3, 17, 3187] ⟨17553997, 5, [(2, 2), (3, 4), (17, 1), (3187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3187
  · decide +kernel

theorem prime_17680843 : Nat.Prime 17680843 := by
  apply nodeValid_prime [2, 3, 109141] ⟨17680843, 13, [(2, 1), (3, 4), (109141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109141
  · decide +kernel

theorem prime_22484747 : Nat.Prime 22484747 := by
  apply nodeValid_prime [2, 11242373] ⟨22484747, 2, [(2, 1), (11242373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11242373
  · decide +kernel

theorem prime_25958431 : Nat.Prime 25958431 := by
  apply nodeValid_prime [2, 3, 5, 288427] ⟨25958431, 6, [(2, 1), (3, 2), (5, 1), (288427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_288427
  · decide +kernel

theorem prime_30087779 : Nat.Prime 30087779 := by
  apply nodeValid_prime [2, 7, 2149127] ⟨30087779, 2, [(2, 1), (7, 1), (2149127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2149127
  · decide +kernel

theorem prime_31262219 : Nat.Prime 31262219 := by
  apply nodeValid_prime [2, 13, 17, 70729] ⟨31262219, 2, [(2, 1), (13, 1), (17, 1), (70729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_70729
  · decide +kernel

theorem prime_34097423 : Nat.Prime 34097423 := by
  apply nodeValid_prime [2, 373, 45707] ⟨34097423, 5, [(2, 1), (373, 1), (45707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_373
    · exact prime_45707
  · decide +kernel

theorem prime_35120777 : Nat.Prime 35120777 := by
  apply nodeValid_prime [2, 17, 258241] ⟨35120777, 3, [(2, 3), (17, 1), (258241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_258241
  · decide +kernel

theorem prime_38642953 : Nat.Prime 38642953 := by
  apply nodeValid_prime [2, 3, 1610123] ⟨38642953, 7, [(2, 3), (3, 1), (1610123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1610123
  · decide +kernel

theorem prime_39836101 : Nat.Prime 39836101 := by
  apply nodeValid_prime [2, 3, 5, 17, 73, 107] ⟨39836101, 2, [(2, 2), (3, 1), (5, 2), (17, 1), (73, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_73
    · exact prime_107
  · decide +kernel

theorem prime_73161943 : Nat.Prime 73161943 := by
  apply nodeValid_prime [2, 3, 7, 23, 53, 1429] ⟨73161943, 5, [(2, 1), (3, 1), (7, 1), (23, 1), (53, 1), (1429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_53
    · exact prime_1429
  · decide +kernel

theorem prime_91998329 : Nat.Prime 91998329 := by
  apply nodeValid_prime [2, 31, 43, 8627] ⟨91998329, 3, [(2, 3), (31, 1), (43, 1), (8627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_8627
  · decide +kernel

theorem prime_105323983 : Nat.Prime 105323983 := by
  apply nodeValid_prime [2, 3, 17553997] ⟨105323983, 3, [(2, 1), (3, 1), (17553997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17553997
  · decide +kernel

theorem prime_110499029 : Nat.Prime 110499029 := by
  apply nodeValid_prime [2, 421, 65617] ⟨110499029, 2, [(2, 2), (421, 1), (65617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_421
    · exact prime_65617
  · decide +kernel

theorem prime_115246361 : Nat.Prime 115246361 := by
  apply nodeValid_prime [2, 5, 2881159] ⟨115246361, 3, [(2, 3), (5, 1), (2881159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2881159
  · decide +kernel

theorem prime_148425001 : Nat.Prime 148425001 := by
  apply nodeValid_prime [2, 3, 5, 1979] ⟨148425001, 22, [(2, 3), (3, 1), (5, 5), (1979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1979
  · decide +kernel

theorem prime_230492723 : Nat.Prime 230492723 := by
  apply nodeValid_prime [2, 115246361] ⟨230492723, 2, [(2, 1), (115246361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_115246361
  · decide +kernel

theorem prime_239016607 : Nat.Prime 239016607 := by
  apply nodeValid_prime [2, 3, 39836101] ⟨239016607, 3, [(2, 1), (3, 1), (39836101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_39836101
  · decide +kernel

theorem prime_271603789 : Nat.Prime 271603789 := by
  apply nodeValid_prime [2, 3, 47, 271, 1777] ⟨271603789, 2, [(2, 2), (3, 1), (47, 1), (271, 1), (1777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_271
    · exact prime_1777
  · decide +kernel

theorem prime_373568501 : Nat.Prime 373568501 := by
  apply nodeValid_prime [2, 5, 19, 39323] ⟨373568501, 2, [(2, 2), (5, 3), (19, 1), (39323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_39323
  · decide +kernel

theorem prime_618287249 : Nat.Prime 618287249 := by
  apply nodeValid_prime [2, 38642953] ⟨618287249, 3, [(2, 4), (38642953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38642953
  · decide +kernel

theorem prime_625900601 : Nat.Prime 625900601 := by
  apply nodeValid_prime [2, 5, 13, 67, 3593] ⟨625900601, 3, [(2, 3), (5, 2), (13, 1), (67, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_67
    · exact prime_3593
  · decide +kernel

theorem prime_994505651 : Nat.Prime 994505651 := by
  apply nodeValid_prime [2, 5, 857, 23209] ⟨994505651, 2, [(2, 1), (5, 2), (857, 1), (23209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_857
    · exact prime_23209
  · decide +kernel

theorem prime_1219770883 : Nat.Prime 1219770883 := by
  apply nodeValid_prime [2, 3, 11, 769, 8011] ⟨1219770883, 2, [(2, 1), (3, 2), (11, 1), (769, 1), (8011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_769
    · exact prime_8011
  · decide +kernel

theorem prime_1447372373 : Nat.Prime 1447372373 := by
  apply nodeValid_prime [2, 199, 1818307] ⟨1447372373, 2, [(2, 2), (199, 1), (1818307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_1818307
  · decide +kernel

theorem prime_1962450043 : Nat.Prime 1962450043 := by
  apply nodeValid_prime [2, 3, 7, 199, 234799] ⟨1962450043, 3, [(2, 1), (3, 1), (7, 1), (199, 1), (234799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_199
    · exact prime_234799
  · decide +kernel

theorem prime_2420887291 : Nat.Prime 2420887291 := by
  apply nodeValid_prime [2, 3, 5, 179, 450817] ⟨2420887291, 3, [(2, 1), (3, 1), (5, 1), (179, 1), (450817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_450817
  · decide +kernel

theorem prime_2887380907 : Nat.Prime 2887380907 := by
  apply nodeValid_prime [2, 3, 2237, 215123] ⟨2887380907, 2, [(2, 1), (3, 1), (2237, 1), (215123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2237
    · exact prime_215123
  · decide +kernel

theorem prime_3321796853 : Nat.Prime 3321796853 := by
  apply nodeValid_prime [2, 11, 983, 76801] ⟨3321796853, 2, [(2, 2), (11, 1), (983, 1), (76801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_983
    · exact prime_76801
  · decide +kernel

theorem prime_4034238697 : Nat.Prime 4034238697 := by
  apply nodeValid_prime [2, 3, 6225677] ⟨4034238697, 5, [(2, 3), (3, 4), (6225677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6225677
  · decide +kernel

theorem prime_4974684947 : Nat.Prime 4974684947 := by
  apply nodeValid_prime [2, 7, 11, 59, 601, 911] ⟨4974684947, 5, [(2, 1), (7, 1), (11, 1), (59, 1), (601, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_59
    · exact prime_601
    · exact prime_911
  · decide +kernel

theorem prime_5802557863 : Nat.Prime 5802557863 := by
  apply nodeValid_prime [2, 3, 73, 13247849] ⟨5802557863, 3, [(2, 1), (3, 1), (73, 1), (13247849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_13247849
  · decide +kernel

theorem prime_5884464431 : Nat.Prime 5884464431 := by
  apply nodeValid_prime [2, 5, 13, 43, 61, 17257] ⟨5884464431, 19, [(2, 1), (5, 1), (13, 1), (43, 1), (61, 1), (17257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_61
    · exact prime_17257
  · decide +kernel

theorem prime_5967033907 : Nat.Prime 5967033907 := by
  apply nodeValid_prime [2, 3, 994505651] ⟨5967033907, 2, [(2, 1), (3, 1), (994505651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_994505651
  · decide +kernel

theorem prime_7849800173 : Nat.Prime 7849800173 := by
  apply nodeValid_prime [2, 1962450043] ⟨7849800173, 2, [(2, 2), (1962450043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1962450043
  · decide +kernel

theorem prime_9929081077 : Nat.Prime 9929081077 := by
  apply nodeValid_prime [2, 3, 1609, 514247] ⟨9929081077, 2, [(2, 2), (3, 1), (1609, 1), (514247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1609
    · exact prime_514247
  · decide +kernel

theorem prime_10680256733 : Nat.Prime 10680256733 := by
  apply nodeValid_prime [2, 17, 991, 158489] ⟨10680256733, 2, [(2, 2), (17, 1), (991, 1), (158489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_991
    · exact prime_158489
  · decide +kernel

theorem prime_11292121051 : Nat.Prime 11292121051 := by
  apply nodeValid_prime [2, 3, 5, 7, 1536343] ⟨11292121051, 2, [(2, 1), (3, 1), (5, 2), (7, 2), (1536343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1536343
  · decide +kernel

theorem prime_16495303819 : Nat.Prime 16495303819 := by
  apply nodeValid_prime [2, 3, 7, 73, 353, 15241] ⟨16495303819, 2, [(2, 1), (3, 1), (7, 1), (73, 1), (353, 1), (15241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_353
    · exact prime_15241
  · decide +kernel

theorem prime_19058401849 : Nat.Prime 19058401849 := by
  apply nodeValid_prime [2, 3, 101, 7862377] ⟨19058401849, 13, [(2, 3), (3, 1), (101, 1), (7862377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_7862377
  · decide +kernel

theorem prime_23161247063 : Nat.Prime 23161247063 := by
  apply nodeValid_prime [2, 31, 373568501] ⟨23161247063, 5, [(2, 1), (31, 1), (373568501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_373568501
  · decide +kernel

theorem prime_28897067119 : Nat.Prime 28897067119 := by
  apply nodeValid_prime [2, 3, 37, 4547, 28627] ⟨28897067119, 3, [(2, 1), (3, 1), (37, 1), (4547, 1), (28627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4547
    · exact prime_28627
  · decide +kernel

theorem prime_37349968969 : Nat.Prime 37349968969 := by
  apply nodeValid_prime [2, 3, 13, 233, 6343] ⟨37349968969, 7, [(2, 3), (3, 5), (13, 1), (233, 1), (6343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_233
    · exact prime_6343
  · decide +kernel

theorem prime_43804769441 : Nat.Prime 43804769441 := by
  apply nodeValid_prime [2, 5, 2269, 120661] ⟨43804769441, 3, [(2, 5), (5, 1), (2269, 1), (120661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2269
    · exact prime_120661
  · decide +kernel

theorem prime_48683400329 : Nat.Prime 48683400329 := by
  apply nodeValid_prime [2, 41, 148425001] ⟨48683400329, 3, [(2, 3), (41, 1), (148425001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_148425001
  · decide +kernel

theorem prime_106041238871 : Nat.Prime 106041238871 := by
  apply nodeValid_prime [2, 5, 7, 577, 2625433] ⟨106041238871, 7, [(2, 1), (5, 1), (7, 1), (577, 1), (2625433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_577
    · exact prime_2625433
  · decide +kernel

theorem prime_220720937999 : Nat.Prime 220720937999 := by
  apply nodeValid_prime [2, 11, 31, 4793, 67523] ⟨220720937999, 7, [(2, 1), (11, 1), (31, 1), (4793, 1), (67523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_4793
    · exact prime_67523
  · decide +kernel

theorem prime_221434359227 : Nat.Prime 221434359227 := by
  apply nodeValid_prime [2, 31, 1151, 1543, 2011] ⟨221434359227, 5, [(2, 1), (31, 1), (1151, 1), (1543, 1), (2011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1151
    · exact prime_1543
    · exact prime_2011
  · decide +kernel

theorem prime_369950749093 : Nat.Prime 369950749093 := by
  apply nodeValid_prime [2, 3, 31, 110499029] ⟨369950749093, 5, [(2, 2), (3, 3), (31, 1), (110499029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_110499029
  · decide +kernel

theorem prime_1108064815453 : Nat.Prime 1108064815453 := by
  apply nodeValid_prime [2, 3, 7, 26951, 163151] ⟨1108064815453, 2, [(2, 2), (3, 2), (7, 1), (26951, 1), (163151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_26951
    · exact prime_163151
  · decide +kernel

theorem prime_1111641650827 : Nat.Prime 1111641650827 := by
  apply nodeValid_prime [2, 3, 7, 9157, 2890429] ⟨1111641650827, 2, [(2, 1), (3, 1), (7, 1), (9157, 1), (2890429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9157
    · exact prime_2890429
  · decide +kernel

theorem prime_1121518343353 : Nat.Prime 1121518343353 := by
  apply nodeValid_prime [2, 3, 11, 17, 283, 883013] ⟨1121518343353, 10, [(2, 3), (3, 1), (11, 1), (17, 1), (283, 1), (883013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_283
    · exact prime_883013
  · decide +kernel

theorem prime_2241236053313 : Nat.Prime 2241236053313 := by
  apply nodeValid_prime [2, 53, 73, 9051257] ⟨2241236053313, 3, [(2, 6), (53, 1), (73, 1), (9051257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_73
    · exact prime_9051257
  · decide +kernel

theorem prime_2243036715533 : Nat.Prime 2243036715533 := by
  apply nodeValid_prime [2, 139, 4034238697] ⟨2243036715533, 2, [(2, 2), (139, 1), (4034238697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_139
    · exact prime_4034238697
  · decide +kernel

theorem prime_2244838335413 : Nat.Prime 2244838335413 := by
  apply nodeValid_prime [2, 31, 43, 9790987] ⟨2244838335413, 2, [(2, 2), (31, 1), (43, 2), (9790987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_43
    · exact prime_9790987
  · decide +kernel

theorem prime_4407296322307 : Nat.Prime 4407296322307 := by
  apply nodeValid_prime [2, 3, 119659, 6138689] ⟨4407296322307, 7, [(2, 1), (3, 1), (119659, 1), (6138689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_119659
    · exact prime_6138689
  · decide +kernel

theorem prime_4407296338343 : Nat.Prime 4407296338343 := by
  apply nodeValid_prime [2, 59, 37349968969] ⟨4407296338343, 5, [(2, 1), (59, 1), (37349968969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_37349968969
  · decide +kernel

theorem prime_4407296338537 : Nat.Prime 4407296338537 := by
  apply nodeValid_prime [2, 3, 7, 13, 3109, 649081] ⟨4407296338537, 5, [(2, 3), (3, 1), (7, 1), (13, 1), (3109, 1), (649081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_3109
    · exact prime_649081
  · decide +kernel

theorem prime_4410856595521 : Nat.Prime 4410856595521 := by
  apply nodeValid_prime [2, 3, 5, 59, 25958431] ⟨4410856595521, 11, [(2, 6), (3, 2), (5, 1), (59, 1), (25958431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_25958431
  · decide +kernel

theorem prime_4410856644203 : Nat.Prime 4410856644203 := by
  apply nodeValid_prime [2, 911, 2420887291] ⟨4410856644203, 2, [(2, 1), (911, 1), (2420887291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_911
    · exact prime_2420887291
  · decide +kernel

theorem prime_4410856645361 : Nat.Prime 4410856645361 := by
  apply nodeValid_prime [2, 5, 11, 43, 1447, 80557] ⟨4410856645361, 3, [(2, 4), (5, 1), (11, 1), (43, 1), (1447, 1), (80557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_43
    · exact prime_1447
    · exact prime_80557
  · decide +kernel

theorem prime_4414418759323 : Nat.Prime 4414418759323 := by
  apply nodeValid_prime [2, 3, 11, 13, 19, 30087779] ⟨4414418759323, 2, [(2, 1), (3, 3), (11, 1), (13, 1), (19, 1), (30087779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_30087779
  · decide +kernel

theorem prime_4414418759981 : Nat.Prime 4414418759981 := by
  apply nodeValid_prime [2, 5, 220720937999] ⟨4414418759981, 2, [(2, 2), (5, 1), (220720937999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_220720937999
  · decide +kernel

theorem prime_4414418808451 : Nat.Prime 4414418808451 := by
  apply nodeValid_prime [2, 3, 5, 7, 61, 1601, 43049] ⟨4414418808451, 11, [(2, 1), (3, 1), (5, 2), (7, 1), (61, 1), (1601, 1), (43049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_61
    · exact prime_1601
    · exact prime_43049
  · decide +kernel

theorem prime_4417982963783 : Nat.Prime 4417982963783 := by
  apply nodeValid_prime [2, 101, 1237, 17680843] ⟨4417982963783, 5, [(2, 1), (101, 1), (1237, 1), (17680843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_1237
    · exact prime_17680843
  · decide +kernel

theorem prime_4417982963789 : Nat.Prime 4417982963789 := by
  apply nodeValid_prime [2, 4621, 239016607] ⟨4417982963789, 2, [(2, 2), (4621, 1), (239016607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4621
    · exact prime_239016607
  · decide +kernel

theorem prime_4417982968537 : Nat.Prime 4417982968537 := by
  apply nodeValid_prime [2, 3, 2729, 22484747] ⟨4417982968537, 5, [(2, 3), (3, 2), (2729, 1), (22484747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2729
    · exact prime_22484747
  · decide +kernel

theorem prime_4421549091607 : Nat.Prime 4421549091607 := by
  apply nodeValid_prime [2, 3, 127, 5802557863] ⟨4421549091607, 3, [(2, 1), (3, 1), (127, 1), (5802557863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_5802557863
  · decide +kernel

theorem prime_4421549228969 : Nat.Prime 4421549228969 := by
  apply nodeValid_prime [2, 29, 19058401849] ⟨4421549228969, 3, [(2, 3), (29, 1), (19058401849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_19058401849
  · decide +kernel

theorem prime_4421549230103 : Nat.Prime 4421549230103 := by
  apply nodeValid_prime [2, 23, 2819, 34097423] ⟨4421549230103, 5, [(2, 1), (23, 1), (2819, 1), (34097423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2819
    · exact prime_34097423
  · decide +kernel

theorem prime_4425117167701 : Nat.Prime 4425117167701 := by
  apply nodeValid_prime [2, 3, 5, 47, 373, 280463] ⟨4425117167701, 2, [(2, 2), (3, 2), (5, 2), (47, 1), (373, 1), (280463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_373
    · exact prime_280463
  · decide +kernel

theorem prime_4425117249071 : Nat.Prime 4425117249071 := by
  apply nodeValid_prime [2, 5, 7, 101, 625900601] ⟨4425117249071, 7, [(2, 1), (5, 1), (7, 1), (101, 1), (625900601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_101
    · exact prime_625900601
  · decide +kernel

theorem prime_4425117252113 : Nat.Prime 4425117252113 := by
  apply nodeValid_prime [2, 47, 5884464431] ⟨4425117252113, 3, [(2, 4), (47, 1), (5884464431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_5884464431
  · decide +kernel

theorem prime_4428687179723 : Nat.Prime 4428687179723 := by
  apply nodeValid_prime [2, 13, 739, 230492723] ⟨4428687179723, 2, [(2, 1), (13, 1), (739, 1), (230492723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_739
    · exact prime_230492723
  · decide +kernel

theorem prime_4428687181403 : Nat.Prime 4428687181403 := by
  apply nodeValid_prime [2, 11, 37, 41, 1709, 77647] ⟨4428687181403, 5, [(2, 1), (11, 1), (37, 1), (41, 1), (1709, 1), (77647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_37
    · exact prime_41
    · exact prime_1709
    · exact prime_77647
  · decide +kernel

theorem prime_4428687184541 : Nat.Prime 4428687184541 := by
  apply nodeValid_prime [2, 5, 221434359227] ⟨4428687184541, 2, [(2, 2), (5, 1), (221434359227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_221434359227
  · decide +kernel

theorem prime_4432259153347 : Nat.Prime 4432259153347 := by
  apply nodeValid_prime [2, 3, 576469, 1281439] ⟨4432259153347, 3, [(2, 1), (3, 1), (576469, 1), (1281439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_576469
    · exact prime_1281439
  · decide +kernel

theorem prime_4432259261813 : Nat.Prime 4432259261813 := by
  apply nodeValid_prime [2, 1108064815453] ⟨4432259261813, 2, [(2, 2), (1108064815453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1108064815453
  · decide +kernel

theorem prime_4432259262437 : Nat.Prime 4432259262437 := by
  apply nodeValid_prime [2, 251, 383, 11526373] ⟨4432259262437, 2, [(2, 2), (251, 1), (383, 1), (11526373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_383
    · exact prime_11526373
  · decide +kernel

theorem prime_4435833076013 : Nat.Prime 4435833076013 := by
  apply nodeValid_prime [2, 13, 619, 2213, 62273] ⟨4435833076013, 2, [(2, 2), (13, 1), (619, 1), (2213, 1), (62273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_619
    · exact prime_2213
    · exact prime_62273
  · decide +kernel

theorem prime_4435833081949 : Nat.Prime 4435833081949 := by
  apply nodeValid_prime [2, 3, 1361, 271603789] ⟨4435833081949, 7, [(2, 2), (3, 1), (1361, 1), (271603789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1361
    · exact prime_271603789
  · decide +kernel

theorem prime_4435833082699 : Nat.Prime 4435833082699 := by
  apply nodeValid_prime [2, 3, 11447, 7176121] ⟨4435833082699, 2, [(2, 1), (3, 3), (11447, 1), (7176121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11447
    · exact prime_7176121
  · decide +kernel

theorem prime_4439408959961 : Nat.Prime 4439408959961 := by
  apply nodeValid_prime [2, 5, 13, 71, 97, 461, 2689] ⟨4439408959961, 6, [(2, 3), (5, 1), (13, 1), (71, 1), (97, 1), (461, 1), (2689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_71
    · exact prime_97
    · exact prime_461
    · exact prime_2689
  · decide +kernel

theorem prime_4439408988241 : Nat.Prime 4439408988241 := by
  apply nodeValid_prime [2, 3, 5, 29, 83, 139, 6143] ⟨4439408988241, 7, [(2, 4), (3, 3), (5, 1), (29, 1), (83, 1), (139, 1), (6143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_83
    · exact prime_139
    · exact prime_6143
  · decide +kernel

theorem prime_4439408989117 : Nat.Prime 4439408989117 := by
  apply nodeValid_prime [2, 3, 369950749093] ⟨4439408989117, 2, [(2, 2), (3, 1), (369950749093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_369950749093
  · decide +kernel

theorem prime_4442986800929 : Nat.Prime 4442986800929 := by
  apply nodeValid_prime [2, 13, 10680256733] ⟨4442986800929, 3, [(2, 5), (13, 1), (10680256733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_10680256733
  · decide +kernel

theorem prime_4442986897919 : Nat.Prime 4442986897919 := by
  apply nodeValid_prime [2, 283, 7849800173] ⟨4442986897919, 11, [(2, 1), (283, 1), (7849800173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_7849800173
  · decide +kernel

theorem prime_4442986898873 : Nat.Prime 4442986898873 := by
  apply nodeValid_prime [2, 5273, 105323983] ⟨4442986898873, 3, [(2, 3), (5273, 1), (105323983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5273
    · exact prime_105323983
  · decide +kernel

theorem prime_4446566596781 : Nat.Prime 4446566596781 := by
  apply nodeValid_prime [2, 5, 7, 11, 2887380907] ⟨4446566596781, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (2887380907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_2887380907
  · decide +kernel

theorem prime_4446566601397 : Nat.Prime 4446566601397 := by
  apply nodeValid_prime [2, 3, 73, 197, 593, 43451] ⟨4446566601397, 2, [(2, 2), (3, 1), (73, 1), (197, 1), (593, 1), (43451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_197
    · exact prime_593
    · exact prime_43451
  · decide +kernel

theorem prime_4446566603309 : Nat.Prime 4446566603309 := by
  apply nodeValid_prime [2, 1111641650827] ⟨4446566603309, 2, [(2, 2), (1111641650827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1111641650827
  · decide +kernel

theorem prime_4450148335463 : Nat.Prime 4450148335463 := by
  apply nodeValid_prime [2, 29, 228509, 335771] ⟨4450148335463, 5, [(2, 1), (29, 1), (228509, 1), (335771, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_228509
    · exact prime_335771
  · decide +kernel

theorem prime_4450148336327 : Nat.Prime 4450148336327 := by
  apply nodeValid_prime [2, 7, 11, 28897067119] ⟨4450148336327, 5, [(2, 1), (7, 1), (11, 1), (28897067119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_28897067119
  · decide +kernel

theorem prime_4450148344919 : Nat.Prime 4450148344919 := by
  apply nodeValid_prime [2, 17, 1789, 73161943] ⟨4450148344919, 7, [(2, 1), (17, 1), (1789, 1), (73161943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1789
    · exact prime_73161943
  · decide +kernel

theorem prime_4453732031131 : Nat.Prime 4453732031131 := by
  apply nodeValid_prime [2, 3, 5, 16495303819] ⟨4453732031131, 3, [(2, 1), (3, 3), (5, 1), (16495303819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_16495303819
  · decide +kernel

theorem prime_4453732032583 : Nat.Prime 4453732032583 := by
  apply nodeValid_prime [2, 3, 7, 106041238871] ⟨4453732032583, 3, [(2, 1), (3, 1), (7, 1), (106041238871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_106041238871
  · decide +kernel

theorem prime_4453732051999 : Nat.Prime 4453732051999 := by
  apply nodeValid_prime [2, 3, 356261, 2083553] ⟨4453732051999, 6, [(2, 1), (3, 1), (356261, 1), (2083553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_356261
    · exact prime_2083553
  · decide +kernel

theorem prime_4457317708147 : Nat.Prime 4457317708147 := by
  apply nodeValid_prime [2, 3, 137587, 5399393] ⟨4457317708147, 19, [(2, 1), (3, 1), (137587, 1), (5399393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137587
    · exact prime_5399393
  · decide +kernel

theorem prime_4457317708517 : Nat.Prime 4457317708517 := by
  apply nodeValid_prime [2, 73, 89, 4099, 41843] ⟨4457317708517, 2, [(2, 2), (73, 1), (89, 1), (4099, 1), (41843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_89
    · exact prime_4099
    · exact prime_41843
  · decide +kernel

theorem prime_4457317712513 : Nat.Prime 4457317712513 := by
  apply nodeValid_prime [2, 7, 4974684947] ⟨4457317712513, 3, [(2, 7), (7, 1), (4974684947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4974684947
  · decide +kernel

theorem prime_4460905331917 : Nat.Prime 4460905331917 := by
  apply nodeValid_prime [2, 3, 11, 6133, 5510311] ⟨4460905331917, 6, [(2, 2), (3, 1), (11, 1), (6133, 1), (5510311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_6133
    · exact prime_5510311
  · decide +kernel

theorem prime_4460905366667 : Nat.Prime 4460905366667 := by
  apply nodeValid_prime [2, 7, 45131, 1008607] ⟨4460905366667, 2, [(2, 1), (7, 2), (45131, 1), (1008607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_45131
    · exact prime_1008607
  · decide +kernel

theorem prime_4460905367227 : Nat.Prime 4460905367227 := by
  apply nodeValid_prime [2, 3, 7, 11, 109, 1097, 2447] ⟨4460905367227, 2, [(2, 1), (3, 2), (7, 1), (11, 2), (109, 1), (1097, 1), (2447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_109
    · exact prime_1097
    · exact prime_2447
  · decide +kernel

theorem prime_4464494909713 : Nat.Prime 4464494909713 := by
  apply nodeValid_prime [2, 3, 337, 91998329] ⟨4464494909713, 5, [(2, 4), (3, 2), (337, 1), (91998329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_337
    · exact prime_91998329
  · decide +kernel

theorem prime_4464494970433 : Nat.Prime 4464494970433 := by
  apply nodeValid_prime [2, 3, 7, 3321796853] ⟨4464494970433, 10, [(2, 6), (3, 1), (7, 1), (3321796853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3321796853
  · decide +kernel

theorem prime_4464494970953 : Nat.Prime 4464494970953 := by
  apply nodeValid_prime [2, 17851, 31262219] ⟨4464494970953, 3, [(2, 3), (17851, 1), (31262219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17851
    · exact prime_31262219
  · decide +kernel

theorem prime_4468086442667 : Nat.Prime 4468086442667 := by
  apply nodeValid_prime [2, 7, 11, 23, 6047, 208609] ⟨4468086442667, 2, [(2, 1), (7, 1), (11, 1), (23, 1), (6047, 1), (208609, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_6047
    · exact prime_208609
  · decide +kernel

theorem prime_4468086482983 : Nat.Prime 4468086482983 := by
  apply nodeValid_prime [2, 3, 17, 43804769441] ⟨4468086482983, 3, [(2, 1), (3, 1), (17, 1), (43804769441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43804769441
  · decide +kernel

theorem prime_4468086484651 : Nat.Prime 4468086484651 := by
  apply nodeValid_prime [2, 3, 5, 9929081077] ⟨4468086484651, 2, [(2, 1), (3, 2), (5, 2), (9929081077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_9929081077
  · decide +kernel

theorem prime_4471679936197 : Nat.Prime 4471679936197 := by
  apply nodeValid_prime [2, 3, 11, 11292121051] ⟨4471679936197, 2, [(2, 2), (3, 2), (11, 1), (11292121051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_11292121051
  · decide +kernel

theorem prime_4471680057079 : Nat.Prime 4471680057079 := by
  apply nodeValid_prime [2, 3, 13, 47, 1219770883] ⟨4471680057079, 7, [(2, 1), (3, 1), (13, 1), (47, 1), (1219770883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_47
    · exact prime_1219770883
  · decide +kernel

theorem prime_4471680057661 : Nat.Prime 4471680057661 := by
  apply nodeValid_prime [2, 3, 5, 41, 2713, 223339] ⟨4471680057661, 2, [(2, 2), (3, 2), (5, 1), (41, 1), (2713, 1), (223339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_2713
    · exact prime_223339
  · decide +kernel

theorem prime_4475275377317 : Nat.Prime 4475275377317 := by
  apply nodeValid_prime [2, 773, 1447372373] ⟨4475275377317, 2, [(2, 2), (773, 1), (1447372373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_773
    · exact prime_1447372373
  · decide +kernel

theorem prime_4475275430251 : Nat.Prime 4475275430251 := by
  apply nodeValid_prime [2, 3, 5, 5967033907] ⟨4475275430251, 10, [(2, 1), (3, 1), (5, 3), (5967033907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5967033907
  · decide +kernel

theorem prime_4475275432363 : Nat.Prime 4475275432363 := by
  apply nodeValid_prime [2, 3, 7, 67141, 529007] ⟨4475275432363, 2, [(2, 1), (3, 2), (7, 1), (67141, 1), (529007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67141
    · exact prime_529007
  · decide +kernel

theorem prime_4478872772783 : Nat.Prime 4478872772783 := by
  apply nodeValid_prime [2, 1318267, 1698773] ⟨4478872772783, 5, [(2, 1), (1318267, 1), (1698773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1318267
    · exact prime_1698773
  · decide +kernel

theorem prime_4478872830269 : Nat.Prime 4478872830269 := by
  apply nodeValid_prime [2, 23, 48683400329] ⟨4478872830269, 2, [(2, 2), (23, 1), (48683400329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_48683400329
  · decide +kernel

theorem prime_4478872831757 : Nat.Prime 4478872831757 := by
  apply nodeValid_prime [2, 1811, 618287249] ⟨4478872831757, 2, [(2, 2), (1811, 1), (618287249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1811
    · exact prime_618287249
  · decide +kernel

theorem prime_4482472106627 : Nat.Prime 4482472106627 := by
  apply nodeValid_prime [2, 2241236053313] ⟨4482472106627, 2, [(2, 1), (2241236053313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2241236053313
  · decide +kernel

theorem prime_4482472109351 : Nat.Prime 4482472109351 := by
  apply nodeValid_prime [2, 5, 12967, 6913661] ⟨4482472109351, 11, [(2, 1), (5, 2), (12967, 1), (6913661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_12967
    · exact prime_6913661
  · decide +kernel

theorem prime_4482472122361 : Nat.Prime 4482472122361 := by
  apply nodeValid_prime [2, 3, 5, 821, 15166031] ⟨4482472122361, 11, [(2, 3), (3, 2), (5, 1), (821, 1), (15166031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_821
    · exact prime_15166031
  · decide +kernel

theorem prime_4486073372827 : Nat.Prime 4486073372827 := by
  apply nodeValid_prime [2, 3, 682289, 1095839] ⟨4486073372827, 3, [(2, 1), (3, 1), (682289, 1), (1095839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_682289
    · exact prime_1095839
  · decide +kernel

theorem prime_4486073373413 : Nat.Prime 4486073373413 := by
  apply nodeValid_prime [2, 1121518343353] ⟨4486073373413, 2, [(2, 2), (1121518343353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1121518343353
  · decide +kernel

theorem prime_4486073431067 : Nat.Prime 4486073431067 := by
  apply nodeValid_prime [2, 2243036715533] ⟨4486073431067, 2, [(2, 1), (2243036715533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2243036715533
  · decide +kernel

theorem prime_4489676670827 : Nat.Prime 4489676670827 := by
  apply nodeValid_prime [2, 2244838335413] ⟨4489676670827, 2, [(2, 1), (2244838335413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2244838335413
  · decide +kernel

theorem prime_4489676671013 : Nat.Prime 4489676671013 := by
  apply nodeValid_prime [2, 13, 1931, 3439427] ⟨4489676671013, 2, [(2, 2), (13, 2), (1931, 1), (3439427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1931
    · exact prime_3439427
  · decide +kernel

theorem prime_4489676697917 : Nat.Prime 4489676697917 := by
  apply nodeValid_prime [2, 23, 27427, 1779299] ⟨4489676697917, 2, [(2, 2), (23, 1), (27427, 1), (1779299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_27427
    · exact prime_1779299
  · decide +kernel

theorem prime_4493281930223 : Nat.Prime 4493281930223 := by
  apply nodeValid_prime [2, 97, 23161247063] ⟨4493281930223, 5, [(2, 1), (97, 1), (23161247063, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_23161247063
  · decide +kernel

theorem prime_4493281967827 : Nat.Prime 4493281967827 := by
  apply nodeValid_prime [2, 3, 21323, 35120777] ⟨4493281967827, 2, [(2, 1), (3, 1), (21323, 1), (35120777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_21323
    · exact prime_35120777
  · decide +kernel

theorem prime_4493281968211 : Nat.Prime 4493281968211 := by
  apply nodeValid_prime [2, 3, 5, 7, 2003, 10682267] ⟨4493281968211, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (2003, 1), (10682267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_2003
    · exact prime_10682267
  · decide +kernel

end Sude.Lucas.Generated
