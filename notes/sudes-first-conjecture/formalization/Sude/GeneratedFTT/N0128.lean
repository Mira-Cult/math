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
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0044
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0053
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0071
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0087
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0120
import Sude.GeneratedFTT.N0122

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_29833 : Nat.Prime 29833 := by
  apply nodeValid_prime [2, 3, 11, 113] ⟨29833, 5, [(2, 3), (3, 1), (11, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
  · decide +kernel

theorem prime_29983 : Nat.Prime 29983 := by
  apply nodeValid_prime [2, 3, 19, 263] ⟨29983, 5, [(2, 1), (3, 1), (19, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_263
  · decide +kernel

theorem prime_33757 : Nat.Prime 33757 := by
  apply nodeValid_prime [2, 3, 29, 97] ⟨33757, 2, [(2, 2), (3, 1), (29, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_97
  · decide +kernel

theorem prime_36097 : Nat.Prime 36097 := by
  apply nodeValid_prime [2, 3, 47] ⟨36097, 5, [(2, 8), (3, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_36541 : Nat.Prime 36541 := by
  apply nodeValid_prime [2, 3, 5, 7, 29] ⟨36541, 10, [(2, 2), (3, 2), (5, 1), (7, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_29
  · decide +kernel

theorem prime_40903 : Nat.Prime 40903 := by
  apply nodeValid_prime [2, 3, 17, 401] ⟨40903, 3, [(2, 1), (3, 1), (17, 1), (401, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_401
  · decide +kernel

theorem prime_42349 : Nat.Prime 42349 := by
  apply nodeValid_prime [2, 3, 3529] ⟨42349, 2, [(2, 2), (3, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3529
  · decide +kernel

theorem prime_43661 : Nat.Prime 43661 := by
  apply nodeValid_prime [2, 5, 37, 59] ⟨43661, 2, [(2, 2), (5, 1), (37, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_59
  · decide +kernel

theorem prime_47407 : Nat.Prime 47407 := by
  apply nodeValid_prime [2, 3, 7901] ⟨47407, 3, [(2, 1), (3, 1), (7901, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7901
  · decide +kernel

theorem prime_48221 : Nat.Prime 48221 := by
  apply nodeValid_prime [2, 5, 2411] ⟨48221, 2, [(2, 2), (5, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2411
  · decide +kernel

theorem prime_52069 : Nat.Prime 52069 := by
  apply nodeValid_prime [2, 3, 4339] ⟨52069, 2, [(2, 2), (3, 1), (4339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4339
  · decide +kernel

theorem prime_59051 : Nat.Prime 59051 := by
  apply nodeValid_prime [2, 5, 1181] ⟨59051, 10, [(2, 1), (5, 2), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1181
  · decide +kernel

theorem prime_70459 : Nat.Prime 70459 := by
  apply nodeValid_prime [2, 3, 11743] ⟨70459, 3, [(2, 1), (3, 1), (11743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11743
  · decide +kernel

theorem prime_77041 : Nat.Prime 77041 := by
  apply nodeValid_prime [2, 3, 5, 107] ⟨77041, 7, [(2, 4), (3, 2), (5, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_77291 : Nat.Prime 77291 := by
  apply nodeValid_prime [2, 5, 59, 131] ⟨77291, 2, [(2, 1), (5, 1), (59, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_59
    · exact prime_131
  · decide +kernel

theorem prime_84481 : Nat.Prime 84481 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨84481, 7, [(2, 9), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_85037 : Nat.Prime 85037 := by
  apply nodeValid_prime [2, 7, 3037] ⟨85037, 2, [(2, 2), (7, 1), (3037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3037
  · decide +kernel

theorem prime_87323 : Nat.Prime 87323 := by
  apply nodeValid_prime [2, 43661] ⟨87323, 2, [(2, 1), (43661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43661
  · decide +kernel

theorem prime_92179 : Nat.Prime 92179 := by
  apply nodeValid_prime [2, 3, 569] ⟨92179, 3, [(2, 1), (3, 4), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_569
  · decide +kernel

theorem prime_92717 : Nat.Prime 92717 := by
  apply nodeValid_prime [2, 13, 1783] ⟨92717, 2, [(2, 2), (13, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1783
  · decide +kernel

theorem prime_96443 : Nat.Prime 96443 := by
  apply nodeValid_prime [2, 48221] ⟨96443, 2, [(2, 1), (48221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_48221
  · decide +kernel

theorem prime_117529 : Nat.Prime 117529 := by
  apply nodeValid_prime [2, 3, 59, 83] ⟨117529, 7, [(2, 3), (3, 1), (59, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_83
  · decide +kernel

theorem prime_125383 : Nat.Prime 125383 := by
  apply nodeValid_prime [2, 3, 20897] ⟨125383, 3, [(2, 1), (3, 1), (20897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20897
  · decide +kernel

theorem prime_129631 : Nat.Prime 129631 := by
  apply nodeValid_prime [2, 3, 5, 29, 149] ⟨129631, 6, [(2, 1), (3, 1), (5, 1), (29, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_149
  · decide +kernel

theorem prime_134789 : Nat.Prime 134789 := by
  apply nodeValid_prime [2, 31, 1087] ⟨134789, 2, [(2, 2), (31, 1), (1087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1087
  · decide +kernel

theorem prime_179899 : Nat.Prime 179899 := by
  apply nodeValid_prime [2, 3, 29983] ⟨179899, 2, [(2, 1), (3, 1), (29983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29983
  · decide +kernel

theorem prime_228131 : Nat.Prime 228131 := by
  apply nodeValid_prime [2, 5, 7, 3259] ⟨228131, 2, [(2, 1), (5, 1), (7, 1), (3259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_3259
  · decide +kernel

theorem prime_238477 : Nat.Prime 238477 := by
  apply nodeValid_prime [2, 3, 7, 17, 167] ⟨238477, 5, [(2, 2), (3, 1), (7, 1), (17, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_167
  · decide +kernel

theorem prime_269579 : Nat.Prime 269579 := by
  apply nodeValid_prime [2, 134789] ⟨269579, 2, [(2, 1), (134789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_134789
  · decide +kernel

theorem prime_280921 : Nat.Prime 280921 := by
  apply nodeValid_prime [2, 3, 5, 2341] ⟨280921, 29, [(2, 3), (3, 1), (5, 1), (2341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2341
  · decide +kernel

theorem prime_283207 : Nat.Prime 283207 := by
  apply nodeValid_prime [2, 3, 7, 11, 613] ⟨283207, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_613
  · decide +kernel

theorem prime_333533 : Nat.Prime 333533 := by
  apply nodeValid_prime [2, 83383] ⟨333533, 2, [(2, 2), (83383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_83383
  · decide +kernel

theorem prime_337457 : Nat.Prime 337457 := by
  apply nodeValid_prime [2, 7, 23, 131] ⟨337457, 3, [(2, 4), (7, 1), (23, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_131
  · decide +kernel

theorem prime_340211 : Nat.Prime 340211 := by
  apply nodeValid_prime [2, 5, 13, 2617] ⟨340211, 7, [(2, 1), (5, 1), (13, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2617
  · decide +kernel

theorem prime_370529 : Nat.Prime 370529 := by
  apply nodeValid_prime [2, 11579] ⟨370529, 3, [(2, 5), (11579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11579
  · decide +kernel

theorem prime_434437 : Nat.Prime 434437 := by
  apply nodeValid_prime [2, 3, 41, 883] ⟨434437, 6, [(2, 2), (3, 1), (41, 1), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_883
  · decide +kernel

theorem prime_466079 : Nat.Prime 466079 := by
  apply nodeValid_prime [2, 397, 587] ⟨466079, 11, [(2, 1), (397, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_397
    · exact prime_587
  · decide +kernel

theorem prime_483643 : Nat.Prime 483643 := by
  apply nodeValid_prime [2, 3, 97, 277] ⟨483643, 2, [(2, 1), (3, 2), (97, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_277
  · decide +kernel

theorem prime_486193 : Nat.Prime 486193 := by
  apply nodeValid_prime [2, 3, 7, 1447] ⟨486193, 5, [(2, 4), (3, 1), (7, 1), (1447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1447
  · decide +kernel

theorem prime_506887 : Nat.Prime 506887 := by
  apply nodeValid_prime [2, 3, 84481] ⟨506887, 5, [(2, 1), (3, 1), (84481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_84481
  · decide +kernel

theorem prime_539159 : Nat.Prime 539159 := by
  apply nodeValid_prime [2, 269579] ⟨539159, 11, [(2, 1), (269579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_269579
  · decide +kernel

theorem prime_542071 : Nat.Prime 542071 := by
  apply nodeValid_prime [2, 3, 5, 19, 317] ⟨542071, 3, [(2, 1), (3, 2), (5, 1), (19, 1), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_317
  · decide +kernel

theorem prime_578659 : Nat.Prime 578659 := by
  apply nodeValid_prime [2, 3, 96443] ⟨578659, 3, [(2, 1), (3, 1), (96443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_96443
  · decide +kernel

theorem prime_736361 : Nat.Prime 736361 := by
  apply nodeValid_prime [2, 5, 41, 449] ⟨736361, 3, [(2, 3), (5, 1), (41, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_449
  · decide +kernel

theorem prime_796561 : Nat.Prime 796561 := by
  apply nodeValid_prime [2, 3, 5, 3319] ⟨796561, 7, [(2, 4), (3, 1), (5, 1), (3319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3319
  · decide +kernel

theorem prime_878221 : Nat.Prime 878221 := by
  apply nodeValid_prime [2, 3, 5, 7, 17, 41] ⟨878221, 2, [(2, 2), (3, 2), (5, 1), (7, 1), (17, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_41
  · decide +kernel

theorem prime_1140973 : Nat.Prime 1140973 := by
  apply nodeValid_prime [2, 3, 7, 17, 47] ⟨1140973, 6, [(2, 2), (3, 1), (7, 1), (17, 2), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_1222523 : Nat.Prime 1222523 := by
  apply nodeValid_prime [2, 7, 87323] ⟨1222523, 2, [(2, 1), (7, 1), (87323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_87323
  · decide +kernel

theorem prime_1235417 : Nat.Prime 1235417 := by
  apply nodeValid_prime [2, 7, 13, 1697] ⟨1235417, 3, [(2, 3), (7, 1), (13, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1697
  · decide +kernel

theorem prime_1285981 : Nat.Prime 1285981 := by
  apply nodeValid_prime [2, 3, 5, 21433] ⟨1285981, 10, [(2, 2), (3, 1), (5, 1), (21433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21433
  · decide +kernel

theorem prime_1483289 : Nat.Prime 1483289 := by
  apply nodeValid_prime [2, 31, 5981] ⟨1483289, 3, [(2, 3), (31, 1), (5981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_5981
  · decide +kernel

theorem prime_1484501 : Nat.Prime 1484501 := by
  apply nodeValid_prime [2, 5, 2969] ⟨1484501, 2, [(2, 2), (5, 3), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2969
  · decide +kernel

theorem prime_1498951 : Nat.Prime 1498951 := by
  apply nodeValid_prime [2, 3, 5, 3331] ⟨1498951, 31, [(2, 1), (3, 2), (5, 2), (3331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3331
  · decide +kernel

theorem prime_1685527 : Nat.Prime 1685527 := by
  apply nodeValid_prime [2, 3, 280921] ⟨1685527, 5, [(2, 1), (3, 1), (280921, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_280921
  · decide +kernel

theorem prime_2011441 : Nat.Prime 2011441 := by
  apply nodeValid_prime [2, 3, 5, 17, 29] ⟨2011441, 14, [(2, 4), (3, 1), (5, 1), (17, 2), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_29
  · decide +kernel

theorem prime_2055223 : Nat.Prime 2055223 := by
  apply nodeValid_prime [2, 3, 13, 8783] ⟨2055223, 3, [(2, 1), (3, 2), (13, 1), (8783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_8783
  · decide +kernel

theorem prime_2286847 : Nat.Prime 2286847 := by
  apply nodeValid_prime [2, 3, 42349] ⟨2286847, 5, [(2, 1), (3, 3), (42349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42349
  · decide +kernel

theorem prime_2539841 : Nat.Prime 2539841 := by
  apply nodeValid_prime [2, 5, 7937] ⟨2539841, 3, [(2, 6), (5, 1), (7937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7937
  · decide +kernel

theorem prime_2699657 : Nat.Prime 2699657 := by
  apply nodeValid_prime [2, 337457] ⟨2699657, 3, [(2, 3), (337457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_337457
  · decide +kernel

theorem prime_2801459 : Nat.Prime 2801459 := by
  apply nodeValid_prime [2, 11, 29, 4391] ⟨2801459, 2, [(2, 1), (11, 1), (29, 1), (4391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_4391
  · decide +kernel

theorem prime_2969003 : Nat.Prime 2969003 := by
  apply nodeValid_prime [2, 1484501] ⟨2969003, 2, [(2, 1), (1484501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1484501
  · decide +kernel

theorem prime_3176513 : Nat.Prime 3176513 := by
  apply nodeValid_prime [2, 49633] ⟨3176513, 3, [(2, 6), (49633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_49633
  · decide +kernel

theorem prime_3563389 : Nat.Prime 3563389 := by
  apply nodeValid_prime [2, 3, 31, 103] ⟨3563389, 2, [(2, 2), (3, 2), (31, 2), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_103
  · decide +kernel

theorem prime_4032101 : Nat.Prime 4032101 := by
  apply nodeValid_prime [2, 5, 61, 661] ⟨4032101, 2, [(2, 2), (5, 2), (61, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_661
  · decide +kernel

theorem prime_5015321 : Nat.Prime 5015321 := by
  apply nodeValid_prime [2, 5, 125383] ⟨5015321, 3, [(2, 3), (5, 1), (125383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_125383
  · decide +kernel

theorem prime_5340971 : Nat.Prime 5340971 := by
  apply nodeValid_prime [2, 5, 389, 1373] ⟨5340971, 2, [(2, 1), (5, 1), (389, 1), (1373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_389
    · exact prime_1373
  · decide +kernel

theorem prime_5863009 : Nat.Prime 5863009 := by
  apply nodeValid_prime [2, 3, 157, 389] ⟨5863009, 7, [(2, 5), (3, 1), (157, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_389
  · decide +kernel

theorem prime_5938007 : Nat.Prime 5938007 := by
  apply nodeValid_prime [2, 2969003] ⟨5938007, 5, [(2, 1), (2969003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2969003
  · decide +kernel

theorem prime_5942081 : Nat.Prime 5942081 := by
  apply nodeValid_prime [2, 5, 31, 599] ⟨5942081, 3, [(2, 6), (5, 1), (31, 1), (599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_599
  · decide +kernel

theorem prime_8358877 : Nat.Prime 8358877 := by
  apply nodeValid_prime [2, 3, 25799] ⟨8358877, 5, [(2, 2), (3, 4), (25799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_25799
  · decide +kernel

theorem prime_8702009 : Nat.Prime 8702009 := by
  apply nodeValid_prime [2, 7, 79, 281] ⟨8702009, 3, [(2, 3), (7, 2), (79, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_281
  · decide +kernel

theorem prime_9558733 : Nat.Prime 9558733 := by
  apply nodeValid_prime [2, 3, 796561] ⟨9558733, 2, [(2, 2), (3, 1), (796561, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_796561
  · decide +kernel

theorem prime_10113163 : Nat.Prime 10113163 := by
  apply nodeValid_prime [2, 3, 1685527] ⟨10113163, 2, [(2, 1), (3, 1), (1685527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1685527
  · decide +kernel

theorem prime_13852217 : Nat.Prime 13852217 := by
  apply nodeValid_prime [2, 7, 19, 47, 277] ⟨13852217, 6, [(2, 3), (7, 1), (19, 1), (47, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_47
    · exact prime_277
  · decide +kernel

theorem prime_23847701 : Nat.Prime 23847701 := by
  apply nodeValid_prime [2, 5, 238477] ⟨23847701, 3, [(2, 2), (5, 2), (238477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_238477
  · decide +kernel

theorem prime_24414757 : Nat.Prime 24414757 := by
  apply nodeValid_prime [2, 3, 157, 12959] ⟨24414757, 2, [(2, 2), (3, 1), (157, 1), (12959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_12959
  · decide +kernel

theorem prime_29035907 : Nat.Prime 29035907 := by
  apply nodeValid_prime [2, 59, 103, 2389] ⟨29035907, 2, [(2, 1), (59, 1), (103, 1), (2389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_103
    · exact prime_2389
  · decide +kernel

theorem prime_29984749 : Nat.Prime 29984749 := by
  apply nodeValid_prime [2, 3, 1117, 2237] ⟨29984749, 2, [(2, 2), (3, 1), (1117, 1), (2237, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1117
    · exact prime_2237
  · decide +kernel

theorem prime_42866587 : Nat.Prime 42866587 := by
  apply nodeValid_prime [2, 3, 7, 340211] ⟨42866587, 3, [(2, 1), (3, 2), (7, 1), (340211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_340211
  · decide +kernel

theorem prime_44463481 : Nat.Prime 44463481 := by
  apply nodeValid_prime [2, 3, 5, 370529] ⟨44463481, 7, [(2, 3), (3, 1), (5, 1), (370529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_370529
  · decide +kernel

theorem prime_53809331 : Nat.Prime 53809331 := by
  apply nodeValid_prime [2, 5, 19, 283207] ⟨53809331, 2, [(2, 1), (5, 1), (19, 1), (283207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_283207
  · decide +kernel

theorem prime_88750621 : Nat.Prime 88750621 := by
  apply nodeValid_prime [2, 3, 5, 7, 53, 443] ⟨88750621, 2, [(2, 2), (3, 3), (5, 1), (7, 1), (53, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_443
  · decide +kernel

theorem prime_91286197 : Nat.Prime 91286197 := by
  apply nodeValid_prime [2, 3, 31, 211, 1163] ⟨91286197, 11, [(2, 2), (3, 1), (31, 1), (211, 1), (1163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_211
    · exact prime_1163
  · decide +kernel

theorem prime_99683653 : Nat.Prime 99683653 := by
  apply nodeValid_prime [2, 3, 19, 23011] ⟨99683653, 2, [(2, 2), (3, 1), (19, 2), (23011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23011
  · decide +kernel

theorem prime_110655847 : Nat.Prime 110655847 := by
  apply nodeValid_prime [2, 3, 7, 878221] ⟨110655847, 3, [(2, 1), (3, 2), (7, 1), (878221, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_878221
  · decide +kernel

theorem prime_113772353 : Nat.Prime 113772353 := by
  apply nodeValid_prime [2, 23, 77291] ⟨113772353, 3, [(2, 6), (23, 1), (77291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_77291
  · decide +kernel

theorem prime_117018593 : Nat.Prime 117018593 := by
  apply nodeValid_prime [2, 41, 79, 1129] ⟨117018593, 3, [(2, 5), (41, 1), (79, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_79
    · exact prime_1129
  · decide +kernel

theorem prime_233219291 : Nat.Prime 233219291 := by
  apply nodeValid_prime [2, 5, 331, 70459] ⟨233219291, 2, [(2, 1), (5, 1), (331, 1), (70459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_331
    · exact prime_70459
  · decide +kernel

theorem prime_234037187 : Nat.Prime 234037187 := by
  apply nodeValid_prime [2, 117018593] ⟨234037187, 2, [(2, 1), (117018593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117018593
  · decide +kernel

theorem prime_239464501 : Nat.Prime 239464501 := by
  apply nodeValid_prime [2, 3, 5, 11, 23, 631] ⟨239464501, 2, [(2, 2), (3, 1), (5, 3), (11, 1), (23, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_631
  · decide +kernel

theorem prime_243338369 : Nat.Prime 243338369 := by
  apply nodeValid_prime [2, 7, 13, 1607] ⟨243338369, 3, [(2, 7), (7, 1), (13, 2), (1607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_1607
  · decide +kernel

theorem prime_382888397 : Nat.Prime 382888397 := by
  apply nodeValid_prime [2, 11, 8702009] ⟨382888397, 2, [(2, 2), (11, 1), (8702009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_8702009
  · decide +kernel

theorem prime_389146091 : Nat.Prime 389146091 := by
  apply nodeValid_prime [2, 5, 659, 59051] ⟨389146091, 2, [(2, 1), (5, 1), (659, 1), (59051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_659
    · exact prime_59051
  · decide +kernel

theorem prime_401466787 : Nat.Prime 401466787 := by
  apply nodeValid_prime [2, 3, 7, 9558733] ⟨401466787, 2, [(2, 1), (3, 1), (7, 1), (9558733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_9558733
  · decide +kernel

theorem prime_411632461 : Nat.Prime 411632461 := by
  apply nodeValid_prime [2, 3, 5, 2286847] ⟨411632461, 2, [(2, 2), (3, 2), (5, 1), (2286847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2286847
  · decide +kernel

theorem prime_428562103 : Nat.Prime 428562103 := by
  apply nodeValid_prime [2, 3, 97, 736361] ⟨428562103, 3, [(2, 1), (3, 1), (97, 1), (736361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_736361
  · decide +kernel

theorem prime_486116251 : Nat.Prime 486116251 := by
  apply nodeValid_prime [2, 3, 5, 129631] ⟨486116251, 3, [(2, 1), (3, 1), (5, 4), (129631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_129631
  · decide +kernel

theorem prime_563939833 : Nat.Prime 563939833 := by
  apply nodeValid_prime [2, 3, 103, 228131] ⟨563939833, 5, [(2, 3), (3, 1), (103, 1), (228131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_228131
  · decide +kernel

theorem prime_585954169 : Nat.Prime 585954169 := by
  apply nodeValid_prime [2, 3, 24414757] ⟨585954169, 7, [(2, 3), (3, 1), (24414757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24414757
  · decide +kernel

theorem prime_1078547731 : Nat.Prime 1078547731 := by
  apply nodeValid_prime [2, 3, 5, 13, 19, 59, 2467] ⟨1078547731, 2, [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (59, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_59
    · exact prime_2467
  · decide +kernel

theorem prime_1764175477 : Nat.Prime 1764175477 := by
  apply nodeValid_prime [2, 3, 7, 17, 1235417] ⟨1764175477, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (1235417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_1235417
  · decide +kernel

theorem prime_2535805001 : Nat.Prime 2535805001 := by
  apply nodeValid_prime [2, 5, 17, 29833] ⟨2535805001, 6, [(2, 3), (5, 4), (17, 1), (29833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_29833
  · decide +kernel

theorem prime_2770003399 : Nat.Prime 2770003399 := by
  apply nodeValid_prime [2, 3, 139, 1303, 2549] ⟨2770003399, 3, [(2, 1), (3, 1), (139, 1), (1303, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_1303
    · exact prime_2549
  · decide +kernel

theorem prime_3162922127 : Nat.Prime 3162922127 := by
  apply nodeValid_prime [2, 7, 13, 31, 439, 1277] ⟨3162922127, 7, [(2, 1), (7, 1), (13, 1), (31, 1), (439, 1), (1277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_31
    · exact prime_439
    · exact prime_1277
  · decide +kernel

theorem prime_3636955103 : Nat.Prime 3636955103 := by
  apply nodeValid_prime [2, 11, 41, 4032101] ⟨3636955103, 5, [(2, 1), (11, 1), (41, 1), (4032101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41
    · exact prime_4032101
  · decide +kernel

theorem prime_4115192353 : Nat.Prime 4115192353 := by
  apply nodeValid_prime [2, 3, 42866587] ⟨4115192353, 5, [(2, 5), (3, 1), (42866587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_42866587
  · decide +kernel

theorem prime_10456496581 : Nat.Prime 10456496581 := by
  apply nodeValid_prime [2, 3, 5, 3347, 52069] ⟨10456496581, 6, [(2, 2), (3, 1), (5, 1), (3347, 1), (52069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3347
    · exact prime_52069
  · decide +kernel

theorem prime_17696356759 : Nat.Prime 17696356759 := by
  apply nodeValid_prime [2, 3, 31, 73, 434437] ⟨17696356759, 6, [(2, 1), (3, 2), (31, 1), (73, 1), (434437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_73
    · exact prime_434437
  · decide +kernel

theorem prime_22707537683 : Nat.Prime 22707537683 := by
  apply nodeValid_prime [2, 211, 53809331] ⟨22707537683, 2, [(2, 1), (211, 1), (53809331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_211
    · exact prime_53809331
  · decide +kernel

theorem prime_44926952849 : Nat.Prime 44926952849 := by
  apply nodeValid_prime [2, 23, 107, 1140973] ⟨44926952849, 3, [(2, 4), (23, 1), (107, 1), (1140973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_107
    · exact prime_1140973
  · decide +kernel

theorem prime_80166473393 : Nat.Prime 80166473393 := by
  apply nodeValid_prime [2, 9293, 539159] ⟨80166473393, 3, [(2, 4), (9293, 1), (539159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9293
    · exact prime_539159
  · decide +kernel

theorem prime_92889967421 : Nat.Prime 92889967421 := by
  apply nodeValid_prime [2, 5, 37, 733, 171251] ⟨92889967421, 2, [(2, 2), (5, 1), (37, 1), (733, 1), (171251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_733
    · exact prime_171251
  · decide +kernel

theorem prime_105001110217 : Nat.Prime 105001110217 := by
  apply nodeValid_prime [2, 3, 486116251] ⟨105001110217, 5, [(2, 3), (3, 3), (486116251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_486116251
  · decide +kernel

theorem prime_119007909731 : Nat.Prime 119007909731 := by
  apply nodeValid_prime [2, 5, 31, 1151, 333533] ⟨119007909731, 2, [(2, 1), (5, 1), (31, 1), (1151, 1), (333533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1151
    · exact prime_333533
  · decide +kernel

theorem prime_119894017081 : Nat.Prime 119894017081 := by
  apply nodeValid_prime [2, 3, 5, 17, 37, 797, 1993] ⟨119894017081, 21, [(2, 3), (3, 1), (5, 1), (17, 1), (37, 1), (797, 1), (1993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_37
    · exact prime_797
    · exact prime_1993
  · decide +kernel

theorem prime_125477958973 : Nat.Prime 125477958973 := by
  apply nodeValid_prime [2, 3, 10456496581] ⟨125477958973, 2, [(2, 2), (3, 1), (10456496581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10456496581
  · decide +kernel

theorem prime_158795093503 : Nat.Prime 158795093503 := by
  apply nodeValid_prime [2, 3, 1759, 5015321] ⟨158795093503, 3, [(2, 1), (3, 2), (1759, 1), (5015321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1759
    · exact prime_5015321
  · decide +kernel

theorem prime_189424449527 : Nat.Prime 189424449527 := by
  apply nodeValid_prime [2, 13, 17, 428562103] ⟨189424449527, 5, [(2, 1), (13, 1), (17, 1), (428562103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_428562103
  · decide +kernel

theorem prime_218079230087 : Nat.Prime 218079230087 := by
  apply nodeValid_prime [2, 43, 2535805001] ⟨218079230087, 5, [(2, 1), (43, 1), (2535805001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2535805001
  · decide +kernel

theorem prime_316177397969 : Nat.Prime 316177397969 := by
  apply nodeValid_prime [2, 6221, 3176513] ⟨316177397969, 3, [(2, 4), (6221, 1), (3176513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6221
    · exact prime_3176513
  · decide +kernel

theorem prime_318298183121 : Nat.Prime 318298183121 := by
  apply nodeValid_prime [2, 5, 23, 41, 89, 47407] ⟨318298183121, 3, [(2, 4), (5, 1), (23, 1), (41, 1), (89, 1), (47407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_41
    · exact prime_89
    · exact prime_47407
  · decide +kernel

theorem prime_477093098719 : Nat.Prime 477093098719 := by
  apply nodeValid_prime [2, 3, 47, 563939833] ⟨477093098719, 3, [(2, 1), (3, 2), (47, 1), (563939833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_563939833
  · decide +kernel

theorem prime_711399146699 : Nat.Prime 711399146699 := by
  apply nodeValid_prime [2, 359, 661, 1498951] ⟨711399146699, 2, [(2, 1), (359, 1), (661, 1), (1498951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_661
    · exact prime_1498951
  · decide +kernel

theorem prime_950649770867 : Nat.Prime 950649770867 := by
  apply nodeValid_prime [2, 167, 479, 5942081] ⟨950649770867, 2, [(2, 1), (167, 1), (479, 1), (5942081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_479
    · exact prime_5942081
  · decide +kernel

theorem prime_958441639301 : Nat.Prime 958441639301 := by
  apply nodeValid_prime [2, 5, 29, 257, 1285981] ⟨958441639301, 7, [(2, 2), (5, 2), (29, 1), (257, 1), (1285981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_257
    · exact prime_1285981
  · decide +kernel

theorem prime_1440861333449 : Nat.Prime 1440861333449 := by
  apply nodeValid_prime [2, 1973, 91286197] ⟨1440861333449, 3, [(2, 3), (1973, 1), (91286197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1973
    · exact prime_91286197
  · decide +kernel

theorem prime_2864683729493 : Nat.Prime 2864683729493 := by
  apply nodeValid_prime [2, 13, 19, 6221, 466079] ⟨2864683729493, 2, [(2, 2), (13, 1), (19, 1), (6221, 1), (466079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_6221
    · exact prime_466079
  · decide +kernel

theorem prime_2877456410021 : Nat.Prime 2877456410021 := by
  apply nodeValid_prime [2, 5, 137, 389, 2699657] ⟨2877456410021, 2, [(2, 2), (5, 1), (137, 1), (389, 1), (2699657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
    · exact prime_389
    · exact prime_2699657
  · decide +kernel

theorem prime_2881722603143 : Nat.Prime 2881722603143 := by
  apply nodeValid_prime [2, 2459, 585954169] ⟨2881722603143, 5, [(2, 1), (2459, 1), (585954169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2459
    · exact prime_585954169
  · decide +kernel

theorem prime_2881722666899 : Nat.Prime 2881722666899 := by
  apply nodeValid_prime [2, 1440861333449] ⟨2881722666899, 2, [(2, 1), (1440861333449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1440861333449
  · decide +kernel

theorem prime_5670059951719 : Nat.Prime 5670059951719 := by
  apply nodeValid_prime [2, 3, 105001110217] ⟨5670059951719, 7, [(2, 1), (3, 3), (105001110217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105001110217
  · decide +kernel

theorem prime_5670059982263 : Nat.Prime 5670059982263 := by
  apply nodeValid_prime [2, 13, 218079230087] ⟨5670059982263, 5, [(2, 1), (13, 1), (218079230087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_218079230087
  · decide +kernel

theorem prime_5670059983079 : Nat.Prime 5670059983079 := by
  apply nodeValid_prime [2, 1607, 1764175477] ⟨5670059983079, 7, [(2, 1), (1607, 1), (1764175477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1607
    · exact prime_1764175477
  · decide +kernel

theorem prime_5674282295839 : Nat.Prime 5674282295839 := by
  apply nodeValid_prime [2, 3, 13, 23, 3162922127] ⟨5674282295839, 3, [(2, 1), (3, 1), (13, 1), (23, 1), (3162922127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_3162922127
  · decide +kernel

theorem prime_5674282296499 : Nat.Prime 5674282296499 := by
  apply nodeValid_prime [2, 3, 97, 197, 743, 2467] ⟨5674282296499, 10, [(2, 1), (3, 4), (97, 1), (197, 1), (743, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_97
    · exact prime_197
    · exact prime_743
    · exact prime_2467
  · decide +kernel

theorem prime_5674282333523 : Nat.Prime 5674282333523 := by
  apply nodeValid_prime [2, 11, 2267, 113772353] ⟨5674282333523, 2, [(2, 1), (11, 1), (2267, 1), (113772353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2267
    · exact prime_113772353
  · decide +kernel

theorem prime_5678506844849 : Nat.Prime 5678506844849 := by
  apply nodeValid_prime [2, 101, 103, 109, 312989] ⟨5678506844849, 3, [(2, 4), (101, 1), (103, 1), (109, 1), (312989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_103
    · exact prime_109
    · exact prime_312989
  · decide +kernel

theorem prime_5678506966739 : Nat.Prime 5678506966739 := by
  apply nodeValid_prime [2, 79, 12829, 2801459] ⟨5678506966739, 2, [(2, 1), (79, 1), (12829, 1), (2801459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_12829
    · exact prime_2801459
  · decide +kernel

theorem prime_5678506967951 : Nat.Prime 5678506967951 := by
  apply nodeValid_prime [2, 5, 41, 2770003399] ⟨5678506967951, 11, [(2, 1), (5, 2), (41, 1), (2770003399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_2770003399
  · decide +kernel

theorem prime_5682733485811 : Nat.Prime 5682733485811 := by
  apply nodeValid_prime [2, 3, 5, 189424449527] ⟨5682733485811, 3, [(2, 1), (3, 1), (5, 1), (189424449527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_189424449527
  · decide +kernel

theorem prime_5682733502081 : Nat.Prime 5682733502081 := by
  apply nodeValid_prime [2, 5, 641, 13852217] ⟨5682733502081, 6, [(2, 7), (5, 1), (641, 1), (13852217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
    · exact prime_13852217
  · decide +kernel

theorem prime_5682733502599 : Nat.Prime 5682733502599 := by
  apply nodeValid_prime [2, 3, 83, 131, 29035907] ⟨5682733502599, 19, [(2, 1), (3, 2), (83, 1), (131, 1), (29035907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_131
    · exact prime_29035907
  · decide +kernel

theorem prime_5686962260437 : Nat.Prime 5686962260437 := by
  apply nodeValid_prime [2, 3, 41, 409, 1277, 2459] ⟨5686962260437, 11, [(2, 2), (3, 3), (41, 1), (409, 1), (1277, 1), (2459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_409
    · exact prime_1277
    · exact prime_2459
  · decide +kernel

theorem prime_5686962291379 : Nat.Prime 5686962291379 := by
  apply nodeValid_prime [2, 3, 157, 18583, 36097] ⟨5686962291379, 3, [(2, 1), (3, 3), (157, 1), (18583, 1), (36097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_18583
    · exact prime_36097
  · decide +kernel

theorem prime_5686962292439 : Nat.Prime 5686962292439 := by
  apply nodeValid_prime [2, 7, 23, 199, 88750621] ⟨5686962292439, 14, [(2, 1), (7, 1), (23, 1), (199, 1), (88750621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_199
    · exact prime_88750621
  · decide +kernel

theorem prime_5691193163443 : Nat.Prime 5691193163443 := by
  apply nodeValid_prime [2, 3, 316177397969] ⟨5691193163443, 2, [(2, 1), (3, 2), (316177397969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_316177397969
  · decide +kernel

theorem prime_5691193172513 : Nat.Prime 5691193172513 := by
  apply nodeValid_prime [2, 443, 401466787] ⟨5691193172513, 3, [(2, 5), (443, 1), (401466787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_443
    · exact prime_401466787
  · decide +kernel

theorem prime_5691193173593 : Nat.Prime 5691193173593 := by
  apply nodeValid_prime [2, 711399146699] ⟨5691193173593, 3, [(2, 3), (711399146699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_711399146699
  · decide +kernel

theorem prime_5695426198793 : Nat.Prime 5695426198793 := by
  apply nodeValid_prime [2, 11, 67, 691, 1093, 1279] ⟨5695426198793, 3, [(2, 3), (11, 1), (67, 1), (691, 1), (1093, 1), (1279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_67
    · exact prime_691
    · exact prime_1093
    · exact prime_1279
  · decide +kernel

theorem prime_5695426216553 : Nat.Prime 5695426216553 := by
  apply nodeValid_prime [2, 173, 4115192353] ⟨5695426216553, 3, [(2, 3), (173, 1), (4115192353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_4115192353
  · decide +kernel

theorem prime_5695426218077 : Nat.Prime 5695426218077 := by
  apply nodeValid_prime [2, 7, 59, 1013, 486193] ⟨5695426218077, 3, [(2, 2), (7, 2), (59, 1), (1013, 1), (486193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_1013
    · exact prime_486193
  · decide +kernel

theorem prime_5699661367277 : Nat.Prime 5699661367277 := by
  apply nodeValid_prime [2, 79, 163, 110655847] ⟨5699661367277, 2, [(2, 2), (79, 1), (163, 1), (110655847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_163
    · exact prime_110655847
  · decide +kernel

theorem prime_5699661400201 : Nat.Prime 5699661400201 := by
  apply nodeValid_prime [2, 3, 5, 179, 1361, 38993] ⟨5699661400201, 7, [(2, 3), (3, 1), (5, 2), (179, 1), (1361, 1), (38993, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
    · exact prime_1361
    · exact prime_38993
  · decide +kernel

theorem prime_5699661400877 : Nat.Prime 5699661400877 := by
  apply nodeValid_prime [2, 47, 24799, 1222523] ⟨5699661400877, 2, [(2, 2), (47, 1), (24799, 1), (1222523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_24799
    · exact prime_1222523
  · decide +kernel

theorem prime_5703898624661 : Nat.Prime 5703898624661 := by
  apply nodeValid_prime [2, 5, 2861, 99683653] ⟨5703898624661, 2, [(2, 2), (5, 1), (2861, 1), (99683653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2861
    · exact prime_99683653
  · decide +kernel

theorem prime_5703898625203 : Nat.Prime 5703898625203 := by
  apply nodeValid_prime [2, 3, 950649770867] ⟨5703898625203, 3, [(2, 1), (3, 1), (950649770867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_950649770867
  · decide +kernel

theorem prime_5703898661759 : Nat.Prime 5703898661759 := by
  apply nodeValid_prime [2, 11, 44221, 5863009] ⟨5703898661759, 11, [(2, 1), (11, 1), (44221, 1), (5863009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_44221
    · exact prime_5863009
  · decide +kernel

theorem prime_5708138014753 : Nat.Prime 5708138014753 := by
  apply nodeValid_prime [2, 3, 881, 1847, 36541] ⟨5708138014753, 10, [(2, 5), (3, 1), (881, 1), (1847, 1), (36541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_881
    · exact prime_1847
    · exact prime_36541
  · decide +kernel

theorem prime_5708138015959 : Nat.Prime 5708138015959 := by
  apply nodeValid_prime [2, 3, 7, 41, 139, 23847701] ⟨5708138015959, 6, [(2, 1), (3, 1), (7, 1), (41, 1), (139, 1), (23847701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_139
    · exact prime_23847701
  · decide +kernel

theorem prime_5708138092123 : Nat.Prime 5708138092123 := by
  apply nodeValid_prime [2, 3, 19, 33757, 1483289] ⟨5708138092123, 2, [(2, 1), (3, 1), (19, 1), (33757, 1), (1483289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_33757
    · exact prime_1483289
  · decide +kernel

theorem prime_5712379660297 : Nat.Prime 5712379660297 := by
  apply nodeValid_prime [2, 3, 113, 234037187] ⟨5712379660297, 5, [(2, 3), (3, 3), (113, 1), (234037187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_234037187
  · decide +kernel

theorem prime_5712379667089 : Nat.Prime 5712379667089 := by
  apply nodeValid_prime [2, 3, 119007909731] ⟨5712379667089, 11, [(2, 4), (3, 1), (119007909731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_119007909731
  · decide +kernel

theorem prime_5712379667899 : Nat.Prime 5712379667899 := by
  apply nodeValid_prime [2, 3, 47, 2003, 10113163] ⟨5712379667899, 2, [(2, 1), (3, 1), (47, 1), (2003, 1), (10113163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_2003
    · exact prime_10113163
  · decide +kernel

theorem prime_5716623325981 : Nat.Prime 5716623325981 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 233, 2539841] ⟨5716623325981, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (23, 1), (233, 1), (2539841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_233
    · exact prime_2539841
  · decide +kernel

theorem prime_5716623326731 : Nat.Prime 5716623326731 := by
  apply nodeValid_prime [2, 3, 5, 92717, 2055223] ⟨5716623326731, 2, [(2, 1), (3, 1), (5, 1), (92717, 1), (2055223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_92717
    · exact prime_2055223
  · decide +kernel

theorem prime_5716623366109 : Nat.Prime 5716623366109 := by
  apply nodeValid_prime [2, 3, 158795093503] ⟨5716623366109, 2, [(2, 2), (3, 2), (158795093503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_158795093503
  · decide +kernel

theorem prime_5720869208231 : Nat.Prime 5720869208231 := by
  apply nodeValid_prime [2, 5, 11, 223, 233219291] ⟨5720869208231, 7, [(2, 1), (5, 1), (11, 1), (223, 1), (233219291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_223
    · exact prime_233219291
  · decide +kernel

theorem prime_5720869288049 : Nat.Prime 5720869288049 := by
  apply nodeValid_prime [2, 409, 461, 1229, 1543] ⟨5720869288049, 3, [(2, 4), (409, 1), (461, 1), (1229, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_409
    · exact prime_461
    · exact prime_1229
    · exact prime_1543
  · decide +kernel

theorem prime_5725117184629 : Nat.Prime 5725117184629 := by
  apply nodeValid_prime [2, 3, 477093098719] ⟨5725117184629, 6, [(2, 2), (3, 1), (477093098719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_477093098719
  · decide +kernel

theorem prime_5725117289909 : Nat.Prime 5725117289909 := by
  apply nodeValid_prime [2, 43, 139, 239464501] ⟨5725117289909, 2, [(2, 2), (43, 1), (139, 1), (239464501, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_139
    · exact prime_239464501
  · decide +kernel

theorem prime_5725117290793 : Nat.Prime 5725117290793 := by
  apply nodeValid_prime [2, 3, 613, 389146091] ⟨5725117290793, 5, [(2, 3), (3, 1), (613, 1), (389146091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_389146091
  · decide +kernel

theorem prime_5729367296179 : Nat.Prime 5729367296179 := by
  apply nodeValid_prime [2, 3, 318298183121] ⟨5729367296179, 2, [(2, 1), (3, 2), (318298183121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_318298183121
  · decide +kernel

theorem prime_5729367458987 : Nat.Prime 5729367458987 := by
  apply nodeValid_prime [2, 2864683729493] ⟨5729367458987, 2, [(2, 1), (2864683729493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2864683729493
  · decide +kernel

theorem prime_5729367459289 : Nat.Prime 5729367459289 := by
  apply nodeValid_prime [2, 3, 11, 19, 47, 71, 101, 3389] ⟨5729367459289, 7, [(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (71, 1), (101, 1), (3389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_47
    · exact prime_71
    · exact prime_101
    · exact prime_3389
  · decide +kernel

theorem prime_5733619555141 : Nat.Prime 5733619555141 := by
  apply nodeValid_prime [2, 3, 5, 59, 311, 578659] ⟨5733619555141, 22, [(2, 2), (3, 3), (5, 1), (59, 1), (311, 1), (578659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_311
    · exact prime_578659
  · decide +kernel

theorem prime_5733619589917 : Nat.Prime 5733619589917 := by
  apply nodeValid_prime [2, 3, 17696356759] ⟨5733619589917, 11, [(2, 2), (3, 4), (17696356759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17696356759
  · decide +kernel

theorem prime_5733619591939 : Nat.Prime 5733619591939 := by
  apply nodeValid_prime [2, 3, 7, 37, 31393, 117529] ⟨5733619591939, 7, [(2, 1), (3, 1), (7, 1), (37, 1), (31393, 1), (117529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_31393
    · exact prime_117529
  · decide +kernel

theorem prime_5737873927627 : Nat.Prime 5737873927627 := by
  apply nodeValid_prime [2, 3, 23, 77041, 179899] ⟨5737873927627, 3, [(2, 1), (3, 2), (23, 1), (77041, 1), (179899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_77041
    · exact prime_179899
  · decide +kernel

theorem prime_5737873928921 : Nat.Prime 5737873928921 := by
  apply nodeValid_prime [2, 5, 7, 19, 1078547731] ⟨5737873928921, 3, [(2, 3), (5, 1), (7, 1), (19, 1), (1078547731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19
    · exact prime_1078547731
  · decide +kernel

theorem prime_5737873956037 : Nat.Prime 5737873956037 := by
  apply nodeValid_prime [2, 3, 61, 85037, 92179] ⟨5737873956037, 5, [(2, 2), (3, 1), (61, 1), (85037, 1), (92179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_85037
    · exact prime_92179
  · decide +kernel

theorem prime_5742130492463 : Nat.Prime 5742130492463 := by
  apply nodeValid_prime [2, 7, 13, 67, 929, 506887] ⟨5742130492463, 5, [(2, 1), (7, 1), (13, 1), (67, 1), (929, 1), (506887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_67
    · exact prime_929
    · exact prime_506887
  · decide +kernel

theorem prime_5742130555151 : Nat.Prime 5742130555151 := by
  apply nodeValid_prime [2, 5, 11, 1249, 8358877] ⟨5742130555151, 7, [(2, 1), (5, 2), (11, 1), (1249, 1), (8358877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_1249
    · exact prime_8358877
  · decide +kernel

theorem prime_5742130555937 : Nat.Prime 5742130555937 := by
  apply nodeValid_prime [2, 37, 1361, 3563389] ⟨5742130555937, 3, [(2, 5), (37, 1), (1361, 1), (3563389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1361
    · exact prime_3563389
  · decide +kernel

theorem prime_5746389062177 : Nat.Prime 5746389062177 := by
  apply nodeValid_prime [2, 7, 67, 382888397] ⟨5746389062177, 3, [(2, 5), (7, 1), (67, 1), (382888397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_67
    · exact prime_382888397
  · decide +kernel

theorem prime_5746389062741 : Nat.Prime 5746389062741 := by
  apply nodeValid_prime [2, 5, 79, 3636955103] ⟨5746389062741, 2, [(2, 2), (5, 1), (79, 1), (3636955103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_3636955103
  · decide +kernel

theorem prime_5746389155561 : Nat.Prime 5746389155561 := by
  apply nodeValid_prime [2, 5, 349, 411632461] ⟨5746389155561, 3, [(2, 3), (5, 1), (349, 1), (411632461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
    · exact prime_411632461
  · decide +kernel

theorem prime_5750649835807 : Nat.Prime 5750649835807 := by
  apply nodeValid_prime [2, 3, 958441639301] ⟨5750649835807, 5, [(2, 1), (3, 1), (958441639301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_958441639301
  · decide +kernel

theorem prime_5750649836291 : Nat.Prime 5750649836291 := by
  apply nodeValid_prime [2, 5, 509, 593, 1171, 1627] ⟨5750649836291, 2, [(2, 1), (5, 1), (509, 1), (593, 1), (1171, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_509
    · exact prime_593
    · exact prime_1171
    · exact prime_1627
  · decide +kernel

theorem prime_5750649964673 : Nat.Prime 5750649964673 := by
  apply nodeValid_prime [2, 44926952849] ⟨5750649964673, 3, [(2, 7), (44926952849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_44926952849
  · decide +kernel

theorem prime_5754912819889 : Nat.Prime 5754912819889 := by
  apply nodeValid_prime [2, 3, 119894017081] ⟨5754912819889, 11, [(2, 4), (3, 1), (119894017081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_119894017081
  · decide +kernel

theorem prime_5754912820043 : Nat.Prime 5754912820043 := by
  apply nodeValid_prime [2, 2877456410021] ⟨5754912820043, 2, [(2, 1), (2877456410021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2877456410021
  · decide +kernel

theorem prime_5754912906073 : Nat.Prime 5754912906073 := by
  apply nodeValid_prime [2, 3, 11, 727, 29984749] ⟨5754912906073, 10, [(2, 3), (3, 1), (11, 1), (727, 1), (29984749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_727
    · exact prime_29984749
  · decide +kernel

theorem prime_5759177980103 : Nat.Prime 5759177980103 := by
  apply nodeValid_prime [2, 31, 92889967421] ⟨5759177980103, 5, [(2, 1), (31, 1), (92889967421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_92889967421
  · decide +kernel

theorem prime_5759177981189 : Nat.Prime 5759177981189 := by
  apply nodeValid_prime [2, 17, 839, 5938007] ⟨5759177981189, 2, [(2, 2), (17, 2), (839, 1), (5938007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_839
    · exact prime_5938007
  · decide +kernel

theorem prime_5759177985611 : Nat.Prime 5759177985611 := by
  apply nodeValid_prime [2, 5, 7, 40903, 2011441] ⟨5759177985611, 2, [(2, 1), (5, 1), (7, 1), (40903, 1), (2011441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_40903
    · exact prime_2011441
  · decide +kernel

theorem prime_5763445206287 : Nat.Prime 5763445206287 := by
  apply nodeValid_prime [2, 2881722603143] ⟨5763445206287, 5, [(2, 1), (2881722603143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2881722603143
  · decide +kernel

theorem prime_5763445333799 : Nat.Prime 5763445333799 := by
  apply nodeValid_prime [2, 2881722666899] ⟨5763445333799, 17, [(2, 1), (2881722666899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2881722666899
  · decide +kernel

theorem prime_5763445334183 : Nat.Prime 5763445334183 := by
  apply nodeValid_prime [2, 64811, 44463481] ⟨5763445334183, 5, [(2, 1), (64811, 1), (44463481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_64811
    · exact prime_44463481
  · decide +kernel

theorem prime_5767714571483 : Nat.Prime 5767714571483 := by
  apply nodeValid_prime [2, 127, 22707537683] ⟨5767714571483, 2, [(2, 1), (127, 1), (22707537683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_22707537683
  · decide +kernel

theorem prime_5767714582367 : Nat.Prime 5767714582367 := by
  apply nodeValid_prime [2, 11, 483643, 542071] ⟨5767714582367, 5, [(2, 1), (11, 1), (483643, 1), (542071, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_483643
    · exact prime_542071
  · decide +kernel

theorem prime_5767714582901 : Nat.Prime 5767714582901 := by
  apply nodeValid_prime [2, 5, 10799, 5340971] ⟨5767714582901, 2, [(2, 2), (5, 2), (10799, 1), (5340971, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_10799
    · exact prime_5340971
  · decide +kernel

theorem prime_5771986084297 : Nat.Prime 5771986084297 := by
  apply nodeValid_prime [2, 3, 80166473393] ⟨5771986084297, 5, [(2, 3), (3, 2), (80166473393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_80166473393
  · decide +kernel

theorem prime_5771986112681 : Nat.Prime 5771986112681 := by
  apply nodeValid_prime [2, 5, 593, 243338369] ⟨5771986112681, 6, [(2, 3), (5, 1), (593, 1), (243338369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_593
    · exact prime_243338369
  · decide +kernel

theorem prime_5771986112759 : Nat.Prime 5771986112759 := by
  apply nodeValid_prime [2, 23, 125477958973] ⟨5771986112759, 11, [(2, 1), (23, 1), (125477958973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_125477958973
  · decide +kernel

end Sude.Lucas.Generated
