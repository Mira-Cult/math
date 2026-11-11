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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0043
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0068
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0076
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0086
import Sude.GeneratedFTT.N0095
import Sude.GeneratedFTT.N0108
import Sude.GeneratedFTT.N0112
import Sude.GeneratedFTT.N0117
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0121

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_11213 : Nat.Prime 11213 := by
  apply nodeValid_prime [2, 2803] ⟨11213, 2, [(2, 2), (2803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2803
  · decide +kernel

theorem prime_13711 : Nat.Prime 13711 := by
  apply nodeValid_prime [2, 3, 5, 457] ⟨13711, 6, [(2, 1), (3, 1), (5, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_457
  · decide +kernel

theorem prime_15121 : Nat.Prime 15121 := by
  apply nodeValid_prime [2, 3, 5, 7] ⟨15121, 11, [(2, 4), (3, 3), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_22367 : Nat.Prime 22367 := by
  apply nodeValid_prime [2, 53, 211] ⟨22367, 5, [(2, 1), (53, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_211
  · decide +kernel

theorem prime_28843 : Nat.Prime 28843 := by
  apply nodeValid_prime [2, 3, 11, 19, 23] ⟨28843, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_33623 : Nat.Prime 33623 := by
  apply nodeValid_prime [2, 16811] ⟨33623, 5, [(2, 1), (16811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_16811
  · decide +kernel

theorem prime_37643 : Nat.Prime 37643 := by
  apply nodeValid_prime [2, 11, 29, 59] ⟨37643, 2, [(2, 1), (11, 1), (29, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_59
  · decide +kernel

theorem prime_43291 : Nat.Prime 43291 := by
  apply nodeValid_prime [2, 3, 5, 13, 37] ⟨43291, 3, [(2, 1), (3, 2), (5, 1), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_43969 : Nat.Prime 43969 := by
  apply nodeValid_prime [2, 3, 229] ⟨43969, 11, [(2, 6), (3, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
  · decide +kernel

theorem prime_44773 : Nat.Prime 44773 := by
  apply nodeValid_prime [2, 3, 7, 13, 41] ⟨44773, 5, [(2, 2), (3, 1), (7, 1), (13, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_48871 : Nat.Prime 48871 := by
  apply nodeValid_prime [2, 3, 5, 181] ⟨48871, 3, [(2, 1), (3, 3), (5, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
  · decide +kernel

theorem prime_55381 : Nat.Prime 55381 := by
  apply nodeValid_prime [2, 3, 5, 13, 71] ⟨55381, 6, [(2, 2), (3, 1), (5, 1), (13, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_71
  · decide +kernel

theorem prime_56501 : Nat.Prime 56501 := by
  apply nodeValid_prime [2, 5, 113] ⟨56501, 3, [(2, 2), (5, 3), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_57287 : Nat.Prime 57287 := by
  apply nodeValid_prime [2, 28643] ⟨57287, 5, [(2, 1), (28643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28643
  · decide +kernel

theorem prime_60811 : Nat.Prime 60811 := by
  apply nodeValid_prime [2, 3, 5, 2027] ⟨60811, 2, [(2, 1), (3, 1), (5, 1), (2027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2027
  · decide +kernel

theorem prime_68611 : Nat.Prime 68611 := by
  apply nodeValid_prime [2, 3, 5, 2287] ⟨68611, 2, [(2, 1), (3, 1), (5, 1), (2287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2287
  · decide +kernel

theorem prime_70121 : Nat.Prime 70121 := by
  apply nodeValid_prime [2, 5, 1753] ⟨70121, 6, [(2, 3), (5, 1), (1753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1753
  · decide +kernel

theorem prime_70969 : Nat.Prime 70969 := by
  apply nodeValid_prime [2, 3, 2957] ⟨70969, 11, [(2, 3), (3, 1), (2957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2957
  · decide +kernel

theorem prime_79537 : Nat.Prime 79537 := by
  apply nodeValid_prime [2, 3, 1657] ⟨79537, 7, [(2, 4), (3, 1), (1657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1657
  · decide +kernel

theorem prime_81883 : Nat.Prime 81883 := by
  apply nodeValid_prime [2, 3, 4549] ⟨81883, 3, [(2, 1), (3, 2), (4549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4549
  · decide +kernel

theorem prime_85429 : Nat.Prime 85429 := by
  apply nodeValid_prime [2, 3, 7, 113] ⟨85429, 6, [(2, 2), (3, 3), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_92959 : Nat.Prime 92959 := by
  apply nodeValid_prime [2, 3, 15493] ⟨92959, 6, [(2, 1), (3, 1), (15493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_15493
  · decide +kernel

theorem prime_115021 : Nat.Prime 115021 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨115021, 2, [(2, 2), (3, 4), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_148667 : Nat.Prime 148667 := by
  apply nodeValid_prime [2, 7, 37, 41] ⟨148667, 2, [(2, 1), (7, 2), (37, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_41
  · decide +kernel

theorem prime_173059 : Nat.Prime 173059 := by
  apply nodeValid_prime [2, 3, 28843] ⟨173059, 2, [(2, 1), (3, 1), (28843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28843
  · decide +kernel

theorem prime_182593 : Nat.Prime 182593 := by
  apply nodeValid_prime [2, 3, 317] ⟨182593, 5, [(2, 6), (3, 2), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_317
  · decide +kernel

theorem prime_186469 : Nat.Prime 186469 := by
  apply nodeValid_prime [2, 3, 41, 379] ⟨186469, 7, [(2, 2), (3, 1), (41, 1), (379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_379
  · decide +kernel

theorem prime_189593 : Nat.Prime 189593 := by
  apply nodeValid_prime [2, 13, 1823] ⟨189593, 5, [(2, 3), (13, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1823
  · decide +kernel

theorem prime_191671 : Nat.Prime 191671 := by
  apply nodeValid_prime [2, 3, 5, 6389] ⟨191671, 23, [(2, 1), (3, 1), (5, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6389
  · decide +kernel

theorem prime_220841 : Nat.Prime 220841 := by
  apply nodeValid_prime [2, 5, 5521] ⟨220841, 3, [(2, 3), (5, 1), (5521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5521
  · decide +kernel

theorem prime_228859 : Nat.Prime 228859 := by
  apply nodeValid_prime [2, 3, 7, 5449] ⟨228859, 7, [(2, 1), (3, 1), (7, 1), (5449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5449
  · decide +kernel

theorem prime_298211 : Nat.Prime 298211 := by
  apply nodeValid_prime [2, 5, 11, 2711] ⟨298211, 2, [(2, 1), (5, 1), (11, 1), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_2711
  · decide +kernel

theorem prime_301463 : Nat.Prime 301463 := by
  apply nodeValid_prime [2, 7, 61, 353] ⟨301463, 5, [(2, 1), (7, 1), (61, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_61
    · exact prime_353
  · decide +kernel

theorem prime_353201 : Nat.Prime 353201 := by
  apply nodeValid_prime [2, 5, 883] ⟨353201, 3, [(2, 4), (5, 2), (883, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_883
  · decide +kernel

theorem prime_400721 : Nat.Prime 400721 := by
  apply nodeValid_prime [2, 5, 5009] ⟨400721, 3, [(2, 4), (5, 1), (5009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5009
  · decide +kernel

theorem prime_447101 : Nat.Prime 447101 := by
  apply nodeValid_prime [2, 5, 17, 263] ⟨447101, 3, [(2, 2), (5, 2), (17, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_263
  · decide +kernel

theorem prime_554633 : Nat.Prime 554633 := by
  apply nodeValid_prime [2, 13, 5333] ⟨554633, 3, [(2, 3), (13, 1), (5333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_5333
  · decide +kernel

theorem prime_596423 : Nat.Prime 596423 := by
  apply nodeValid_prime [2, 298211] ⟨596423, 5, [(2, 1), (298211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_298211
  · decide +kernel

theorem prime_638201 : Nat.Prime 638201 := by
  apply nodeValid_prime [2, 5, 3191] ⟨638201, 6, [(2, 3), (5, 2), (3191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3191
  · decide +kernel

theorem prime_675841 : Nat.Prime 675841 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨675841, 7, [(2, 12), (3, 1), (5, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_722069 : Nat.Prime 722069 := by
  apply nodeValid_prime [2, 97, 1861] ⟨722069, 2, [(2, 2), (97, 1), (1861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1861
  · decide +kernel

theorem prime_731267 : Nat.Prime 731267 := by
  apply nodeValid_prime [2, 127, 2879] ⟨731267, 2, [(2, 1), (127, 1), (2879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_2879
  · decide +kernel

theorem prime_756043 : Nat.Prime 756043 := by
  apply nodeValid_prime [2, 3, 7, 47, 383] ⟨756043, 2, [(2, 1), (3, 1), (7, 1), (47, 1), (383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_383
  · decide +kernel

theorem prime_804313 : Nat.Prime 804313 := by
  apply nodeValid_prime [2, 3, 11171] ⟨804313, 5, [(2, 3), (3, 2), (11171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11171
  · decide +kernel

theorem prime_805213 : Nat.Prime 805213 := by
  apply nodeValid_prime [2, 3, 22367] ⟨805213, 2, [(2, 2), (3, 2), (22367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22367
  · decide +kernel

theorem prime_876751 : Nat.Prime 876751 := by
  apply nodeValid_prime [2, 3, 5, 7, 167] ⟨876751, 6, [(2, 1), (3, 1), (5, 3), (7, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_167
  · decide +kernel

theorem prime_894203 : Nat.Prime 894203 := by
  apply nodeValid_prime [2, 447101] ⟨894203, 2, [(2, 1), (447101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_447101
  · decide +kernel

theorem prime_914293 : Nat.Prime 914293 := by
  apply nodeValid_prime [2, 3, 109, 233] ⟨914293, 2, [(2, 2), (3, 2), (109, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_233
  · decide +kernel

theorem prime_1047341 : Nat.Prime 1047341 := by
  apply nodeValid_prime [2, 5, 7, 7481] ⟨1047341, 2, [(2, 2), (5, 1), (7, 1), (7481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7481
  · decide +kernel

theorem prime_1176671 : Nat.Prime 1176671 := by
  apply nodeValid_prime [2, 5, 11, 19, 563] ⟨1176671, 11, [(2, 1), (5, 1), (11, 1), (19, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_563
  · decide +kernel

theorem prime_1192847 : Nat.Prime 1192847 := by
  apply nodeValid_prime [2, 596423] ⟨1192847, 5, [(2, 1), (596423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_596423
  · decide +kernel

theorem prime_1231171 : Nat.Prime 1231171 := by
  apply nodeValid_prime [2, 3, 5, 41039] ⟨1231171, 2, [(2, 1), (3, 1), (5, 1), (41039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41039
  · decide +kernel

theorem prime_1309163 : Nat.Prime 1309163 := by
  apply nodeValid_prime [2, 101, 6481] ⟨1309163, 2, [(2, 1), (101, 1), (6481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_6481
  · decide +kernel

theorem prime_1489051 : Nat.Prime 1489051 := by
  apply nodeValid_prime [2, 3, 5, 1103] ⟨1489051, 3, [(2, 1), (3, 3), (5, 2), (1103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1103
  · decide +kernel

theorem prime_1591637 : Nat.Prime 1591637 := by
  apply nodeValid_prime [2, 29, 13721] ⟨1591637, 2, [(2, 2), (29, 1), (13721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_13721
  · decide +kernel

theorem prime_1799621 : Nat.Prime 1799621 := by
  apply nodeValid_prime [2, 5, 17, 67, 79] ⟨1799621, 2, [(2, 2), (5, 1), (17, 1), (67, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_67
    · exact prime_79
  · decide +kernel

theorem prime_1815959 : Nat.Prime 1815959 := by
  apply nodeValid_prime [2, 167, 5437] ⟨1815959, 13, [(2, 1), (167, 1), (5437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_167
    · exact prime_5437
  · decide +kernel

theorem prime_2094683 : Nat.Prime 2094683 := by
  apply nodeValid_prime [2, 1047341] ⟨2094683, 2, [(2, 1), (1047341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1047341
  · decide +kernel

theorem prime_2353343 : Nat.Prime 2353343 := by
  apply nodeValid_prime [2, 1176671] ⟨2353343, 5, [(2, 1), (1176671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1176671
  · decide +kernel

theorem prime_3599243 : Nat.Prime 3599243 := by
  apply nodeValid_prime [2, 1799621] ⟨3599243, 2, [(2, 1), (1799621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1799621
  · decide +kernel

theorem prime_3631919 : Nat.Prime 3631919 := by
  apply nodeValid_prime [2, 1815959] ⟨3631919, 7, [(2, 1), (1815959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1815959
  · decide +kernel

theorem prime_3907009 : Nat.Prime 3907009 := by
  apply nodeValid_prime [2, 3, 7, 17, 19] ⟨3907009, 13, [(2, 6), (3, 3), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_4893857 : Nat.Prime 4893857 := by
  apply nodeValid_prime [2, 11, 13903] ⟨4893857, 3, [(2, 5), (11, 1), (13903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13903
  · decide +kernel

theorem prime_7089001 : Nat.Prime 7089001 := by
  apply nodeValid_prime [2, 3, 5, 17, 139] ⟨7089001, 21, [(2, 3), (3, 1), (5, 3), (17, 1), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_139
  · decide +kernel

theorem prime_7282853 : Nat.Prime 7282853 := by
  apply nodeValid_prime [2, 19, 79, 1213] ⟨7282853, 2, [(2, 2), (19, 1), (79, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_79
    · exact prime_1213
  · decide +kernel

theorem prime_7783751 : Nat.Prime 7783751 := by
  apply nodeValid_prime [2, 5, 13, 479] ⟨7783751, 34, [(2, 1), (5, 4), (13, 1), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_479
  · decide +kernel

theorem prime_8069041 : Nat.Prime 8069041 := by
  apply nodeValid_prime [2, 3, 5, 7, 1601] ⟨8069041, 13, [(2, 4), (3, 2), (5, 1), (7, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_1601
  · decide +kernel

theorem prime_8795557 : Nat.Prime 8795557 := by
  apply nodeValid_prime [2, 3, 7, 11, 19, 167] ⟨8795557, 5, [(2, 2), (3, 2), (7, 1), (11, 1), (19, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_167
  · decide +kernel

theorem prime_15628037 : Nat.Prime 15628037 := by
  apply nodeValid_prime [2, 3907009] ⟨15628037, 2, [(2, 2), (3907009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3907009
  · decide +kernel

theorem prime_17104231 : Nat.Prime 17104231 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 443] ⟨17104231, 6, [(2, 1), (3, 3), (5, 1), (11, 1), (13, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_443
  · decide +kernel

theorem prime_20050451 : Nat.Prime 20050451 := by
  apply nodeValid_prime [2, 5, 7, 57287] ⟨20050451, 2, [(2, 1), (5, 2), (7, 1), (57287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_57287
  · decide +kernel

theorem prime_20819047 : Nat.Prime 20819047 := by
  apply nodeValid_prime [2, 3, 71, 48871] ⟨20819047, 3, [(2, 1), (3, 1), (71, 1), (48871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_48871
  · decide +kernel

theorem prime_28240117 : Nat.Prime 28240117 := by
  apply nodeValid_prime [2, 3, 2353343] ⟨28240117, 2, [(2, 2), (3, 1), (2353343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2353343
  · decide +kernel

theorem prime_33781147 : Nat.Prime 33781147 := by
  apply nodeValid_prime [2, 3, 7, 804313] ⟨33781147, 2, [(2, 1), (3, 1), (7, 1), (804313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_804313
  · decide +kernel

theorem prime_33797651 : Nat.Prime 33797651 := by
  apply nodeValid_prime [2, 5, 37, 18269] ⟨33797651, 2, [(2, 1), (5, 2), (37, 1), (18269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_18269
  · decide +kernel

theorem prime_40100903 : Nat.Prime 40100903 := by
  apply nodeValid_prime [2, 20050451] ⟨40100903, 5, [(2, 1), (20050451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_20050451
  · decide +kernel

theorem prime_45142453 : Nat.Prime 45142453 := by
  apply nodeValid_prime [2, 3, 349, 3593] ⟨45142453, 2, [(2, 2), (3, 2), (349, 1), (3593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_3593
  · decide +kernel

theorem prime_45385247 : Nat.Prime 45385247 := by
  apply nodeValid_prime [2, 157, 144539] ⟨45385247, 5, [(2, 1), (157, 1), (144539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_144539
  · decide +kernel

theorem prime_46376611 : Nat.Prime 46376611 := by
  apply nodeValid_prime [2, 3, 5, 7, 220841] ⟨46376611, 10, [(2, 1), (3, 1), (5, 1), (7, 1), (220841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_220841
  · decide +kernel

theorem prime_71552521 : Nat.Prime 71552521 := by
  apply nodeValid_prime [2, 3, 5, 13, 15289] ⟨71552521, 28, [(2, 3), (3, 2), (5, 1), (13, 1), (15289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_15289
  · decide +kernel

theorem prime_90178843 : Nat.Prime 90178843 := by
  apply nodeValid_prime [2, 3, 13, 37, 31247] ⟨90178843, 3, [(2, 1), (3, 1), (13, 1), (37, 1), (31247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
    · exact prime_31247
  · decide +kernel

theorem prime_96342097 : Nat.Prime 96342097 := by
  apply nodeValid_prime [2, 3, 179, 11213] ⟨96342097, 5, [(2, 4), (3, 1), (179, 1), (11213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_11213
  · decide +kernel

theorem prime_97877141 : Nat.Prime 97877141 := by
  apply nodeValid_prime [2, 5, 4893857] ⟨97877141, 2, [(2, 2), (5, 1), (4893857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4893857
  · decide +kernel

theorem prime_104346191 : Nat.Prime 104346191 := by
  apply nodeValid_prime [2, 5, 13, 149, 5387] ⟨104346191, 11, [(2, 1), (5, 1), (13, 1), (149, 1), (5387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_149
    · exact prime_5387
  · decide +kernel

theorem prime_112960469 : Nat.Prime 112960469 := by
  apply nodeValid_prime [2, 28240117] ⟨112960469, 2, [(2, 2), (28240117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28240117
  · decide +kernel

theorem prime_131509813 : Nat.Prime 131509813 := by
  apply nodeValid_prime [2, 3, 7, 31, 50503] ⟨131509813, 2, [(2, 2), (3, 1), (7, 1), (31, 1), (50503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_50503
  · decide +kernel

theorem prime_152540599 : Nat.Prime 152540599 := by
  apply nodeValid_prime [2, 3, 7, 3631919] ⟨152540599, 3, [(2, 1), (3, 1), (7, 1), (3631919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3631919
  · decide +kernel

theorem prime_202785907 : Nat.Prime 202785907 := by
  apply nodeValid_prime [2, 3, 33797651] ⟨202785907, 3, [(2, 1), (3, 1), (33797651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33797651
  · decide +kernel

theorem prime_260622077 : Nat.Prime 260622077 := by
  apply nodeValid_prime [2, 11, 13, 41, 11113] ⟨260622077, 2, [(2, 2), (11, 1), (13, 1), (41, 1), (11113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_41
    · exact prime_11113
  · decide +kernel

theorem prime_293592751 : Nat.Prime 293592751 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 1873] ⟨293592751, 3, [(2, 1), (3, 1), (5, 3), (11, 1), (19, 1), (1873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_1873
  · decide +kernel

theorem prime_377110739 : Nat.Prime 377110739 := by
  apply nodeValid_prime [2, 2689, 70121] ⟨377110739, 2, [(2, 1), (2689, 1), (70121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2689
    · exact prime_70121
  · decide +kernel

theorem prime_478918469 : Nat.Prime 478918469 := by
  apply nodeValid_prime [2, 7, 17104231] ⟨478918469, 2, [(2, 2), (7, 1), (17104231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17104231
  · decide +kernel

theorem prime_662861359 : Nat.Prime 662861359 := by
  apply nodeValid_prime [2, 3, 463, 79537] ⟨662861359, 3, [(2, 1), (3, 2), (463, 1), (79537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_463
    · exact prime_79537
  · decide +kernel

theorem prime_668402629 : Nat.Prime 668402629 := by
  apply nodeValid_prime [2, 3, 139, 400721] ⟨668402629, 2, [(2, 2), (3, 1), (139, 1), (400721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
    · exact prime_400721
  · decide +kernel

theorem prime_830245243 : Nat.Prime 830245243 := by
  apply nodeValid_prime [2, 3, 19, 7282853] ⟨830245243, 2, [(2, 1), (3, 1), (19, 1), (7282853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_7282853
  · decide +kernel

theorem prime_1180016423 : Nat.Prime 1180016423 := by
  apply nodeValid_prime [2, 13, 45385247] ⟨1180016423, 5, [(2, 1), (13, 1), (45385247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_45385247
  · decide +kernel

theorem prime_1212650779 : Nat.Prime 1212650779 := by
  apply nodeValid_prime [2, 3, 251, 805213] ⟨1212650779, 10, [(2, 1), (3, 1), (251, 1), (805213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_251
    · exact prime_805213
  · decide +kernel

theorem prime_1591061863 : Nat.Prime 1591061863 := by
  apply nodeValid_prime [2, 3, 13, 19, 71, 15121] ⟨1591061863, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (71, 1), (15121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_71
    · exact prime_15121
  · decide +kernel

theorem prime_2890262911 : Nat.Prime 2890262911 := by
  apply nodeValid_prime [2, 3, 5, 96342097] ⟨2890262911, 3, [(2, 1), (3, 1), (5, 1), (96342097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_96342097
  · decide +kernel

theorem prime_4256742781 : Nat.Prime 4256742781 := by
  apply nodeValid_prime [2, 3, 5, 79, 11087] ⟨4256742781, 2, [(2, 2), (3, 5), (5, 1), (79, 1), (11087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79
    · exact prime_11087
  · decide +kernel

theorem prime_4415426149 : Nat.Prime 4415426149 := by
  apply nodeValid_prime [2, 3, 7, 457, 115021] ⟨4415426149, 2, [(2, 2), (3, 1), (7, 1), (457, 1), (115021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_457
    · exact prime_115021
  · decide +kernel

theorem prime_4724951503 : Nat.Prime 4724951503 := by
  apply nodeValid_prime [2, 3, 19, 23, 193, 9337] ⟨4724951503, 6, [(2, 1), (3, 1), (19, 1), (23, 1), (193, 1), (9337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_193
    · exact prime_9337
  · decide +kernel

theorem prime_5762225389 : Nat.Prime 5762225389 := by
  apply nodeValid_prime [2, 3, 67, 163, 43969] ⟨5762225389, 2, [(2, 2), (3, 1), (67, 1), (163, 1), (43969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_163
    · exact prime_43969
  · decide +kernel

theorem prime_6777628141 : Nat.Prime 6777628141 := by
  apply nodeValid_prime [2, 3, 5, 112960469] ⟨6777628141, 6, [(2, 2), (3, 1), (5, 1), (112960469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_112960469
  · decide +kernel

theorem prime_12126507791 : Nat.Prime 12126507791 := by
  apply nodeValid_prime [2, 5, 1212650779] ⟨12126507791, 13, [(2, 1), (5, 1), (1212650779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1212650779
  · decide +kernel

theorem prime_15485272727 : Nat.Prime 15485272727 := by
  apply nodeValid_prime [2, 7, 11, 19, 756043] ⟨15485272727, 5, [(2, 1), (7, 2), (11, 1), (19, 1), (756043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_756043
  · decide +kernel

theorem prime_33864012979 : Nat.Prime 33864012979 := by
  apply nodeValid_prime [2, 3, 37, 152540599] ⟨33864012979, 2, [(2, 1), (3, 1), (37, 1), (152540599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_152540599
  · decide +kernel

theorem prime_62518178159 : Nat.Prime 62518178159 := by
  apply nodeValid_prime [2, 43291, 722069] ⟨62518178159, 13, [(2, 1), (43291, 1), (722069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43291
    · exact prime_722069
  · decide +kernel

theorem prime_98373224041 : Nat.Prime 98373224041 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 47, 191671] ⟨98373224041, 29, [(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (47, 1), (191671, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_47
    · exact prime_191671
  · decide +kernel

theorem prime_115280181781 : Nat.Prime 115280181781 := by
  apply nodeValid_prime [2, 3, 5, 43, 1187, 37643] ⟨115280181781, 6, [(2, 2), (3, 1), (5, 1), (43, 1), (1187, 1), (37643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_1187
    · exact prime_37643
  · decide +kernel

theorem prime_140040727273 : Nat.Prime 140040727273 := by
  apply nodeValid_prime [2, 3, 11239, 173059] ⟨140040727273, 7, [(2, 3), (3, 2), (11239, 1), (173059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11239
    · exact prime_173059
  · decide +kernel

theorem prime_141748545091 : Nat.Prime 141748545091 := by
  apply nodeValid_prime [2, 3, 5, 4724951503] ⟨141748545091, 2, [(2, 1), (3, 1), (5, 1), (4724951503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4724951503
  · decide +kernel

theorem prime_359674642531 : Nat.Prime 359674642531 := by
  apply nodeValid_prime [2, 3, 5, 7, 53, 157, 68611] ⟨359674642531, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (53, 1), (157, 1), (68611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_53
    · exact prime_157
    · exact prime_68611
  · decide +kernel

theorem prime_363795233731 : Nat.Prime 363795233731 := by
  apply nodeValid_prime [2, 3, 5, 12126507791] ⟨363795233731, 3, [(2, 1), (3, 1), (5, 1), (12126507791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12126507791
  · decide +kernel

theorem prime_646491237703 : Nat.Prime 646491237703 := by
  apply nodeValid_prime [2, 3, 367, 293592751] ⟨646491237703, 3, [(2, 1), (3, 1), (367, 1), (293592751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
    · exact prime_293592751
  · decide +kernel

theorem prime_1088286314293 : Nat.Prime 1088286314293 := by
  apply nodeValid_prime [2, 3, 19, 1591061863] ⟨1088286314293, 11, [(2, 2), (3, 2), (19, 1), (1591061863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1591061863
  · decide +kernel

theorem prime_3227845089869 : Nat.Prime 3227845089869 := by
  apply nodeValid_prime [2, 7, 115280181781] ⟨3227845089869, 2, [(2, 2), (7, 1), (115280181781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_115280181781
  · decide +kernel

theorem prime_3274157103641 : Nat.Prime 3274157103641 := by
  apply nodeValid_prime [2, 5, 23, 1699, 2094683] ⟨3274157103641, 3, [(2, 3), (5, 1), (23, 1), (1699, 1), (2094683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1699
    · exact prime_2094683
  · decide +kernel

theorem prime_6441873454433 : Nat.Prime 6441873454433 := by
  apply nodeValid_prime [2, 13, 15485272727] ⟨6441873454433, 3, [(2, 5), (13, 1), (15485272727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_15485272727
  · decide +kernel

theorem prime_6441873454559 : Nat.Prime 6441873454559 := by
  apply nodeValid_prime [2, 23, 140040727273] ⟨6441873454559, 7, [(2, 1), (23, 1), (140040727273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_140040727273
  · decide +kernel

theorem prime_6441873465631 : Nat.Prime 6441873465631 := by
  apply nodeValid_prime [2, 3, 5, 3001, 71552521] ⟨6441873465631, 3, [(2, 1), (3, 1), (5, 1), (3001, 1), (71552521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3001
    · exact prime_71552521
  · decide +kernel

theorem prime_6446476799467 : Nat.Prime 6446476799467 := by
  apply nodeValid_prime [2, 3, 11, 81883, 1192847] ⟨6446476799467, 2, [(2, 1), (3, 1), (11, 1), (81883, 1), (1192847, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_81883
    · exact prime_1192847
  · decide +kernel

theorem prime_6446476935247 : Nat.Prime 6446476935247 := by
  apply nodeValid_prime [2, 3, 37, 1733, 2557, 6553] ⟨6446476935247, 13, [(2, 1), (3, 1), (37, 1), (1733, 1), (2557, 1), (6553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1733
    · exact prime_2557
    · exact prime_6553
  · decide +kernel

theorem prime_6446476938133 : Nat.Prime 6446476938133 := by
  apply nodeValid_prime [2, 3, 7, 11, 31, 37, 675841] ⟨6446476938133, 2, [(2, 2), (3, 3), (7, 1), (11, 1), (31, 1), (37, 1), (675841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_37
    · exact prime_675841
  · decide +kernel

theorem prime_6451082363311 : Nat.Prime 6451082363311 := by
  apply nodeValid_prime [2, 3, 5, 13, 97877141] ⟨6451082363311, 11, [(2, 1), (3, 1), (5, 1), (13, 3), (97877141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_97877141
  · decide +kernel

theorem prime_6451082366903 : Nat.Prime 6451082366903 := by
  apply nodeValid_prime [2, 24527, 131509813] ⟨6451082366903, 5, [(2, 1), (24527, 1), (131509813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_24527
    · exact prime_131509813
  · decide +kernel

theorem prime_6451082367881 : Nat.Prime 6451082367881 := by
  apply nodeValid_prime [2, 5, 461, 6317, 55381] ⟨6451082367881, 3, [(2, 3), (5, 1), (461, 1), (6317, 1), (55381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_461
    · exact prime_6317
    · exact prime_55381
  · decide +kernel

theorem prime_6455690144789 : Nat.Prime 6455690144789 := by
  apply nodeValid_prime [2, 15467, 104346191] ⟨6455690144789, 2, [(2, 2), (15467, 1), (104346191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_15467
    · exact prime_104346191
  · decide +kernel

theorem prime_6455690179739 : Nat.Prime 6455690179739 := by
  apply nodeValid_prime [2, 3227845089869] ⟨6455690179739, 2, [(2, 1), (3227845089869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3227845089869
  · decide +kernel

theorem prime_6455690179747 : Nat.Prime 6455690179747 := by
  apply nodeValid_prime [2, 3, 313, 733, 14983] ⟨6455690179747, 2, [(2, 1), (3, 1), (313, 2), (733, 1), (14983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
    · exact prime_733
    · exact prime_14983
  · decide +kernel

theorem prime_6460300044571 : Nat.Prime 6460300044571 := by
  apply nodeValid_prime [2, 3, 5, 41, 56501, 92959] ⟨6460300044571, 3, [(2, 1), (3, 1), (5, 1), (41, 1), (56501, 1), (92959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_56501
    · exact prime_92959
  · decide +kernel

theorem prime_6460300044677 : Nat.Prime 6460300044677 := by
  apply nodeValid_prime [2, 6197, 260622077] ⟨6460300044677, 2, [(2, 2), (6197, 1), (260622077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6197
    · exact prime_260622077
  · decide +kernel

theorem prime_6460300157749 : Nat.Prime 6460300157749 := by
  apply nodeValid_prime [2, 3, 137, 487, 8069041] ⟨6460300157749, 2, [(2, 2), (3, 1), (137, 1), (487, 1), (8069041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_487
    · exact prime_8069041
  · decide +kernel

theorem prime_6464912376259 : Nat.Prime 6464912376259 := by
  apply nodeValid_prime [2, 3, 7, 947, 3637, 14897] ⟨6464912376259, 2, [(2, 1), (3, 2), (7, 1), (947, 1), (3637, 1), (14897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_947
    · exact prime_3637
    · exact prime_14897
  · decide +kernel

theorem prime_6464912377031 : Nat.Prime 6464912377031 := by
  apply nodeValid_prime [2, 5, 646491237703] ⟨6464912377031, 22, [(2, 1), (5, 1), (646491237703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_646491237703
  · decide +kernel

theorem prime_6464912396783 : Nat.Prime 6464912396783 := by
  apply nodeValid_prime [2, 7, 107, 60811, 70969] ⟨6464912396783, 5, [(2, 1), (7, 1), (107, 1), (60811, 1), (70969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
    · exact prime_60811
    · exact prime_70969
  · decide +kernel

theorem prime_6469526863841 : Nat.Prime 6469526863841 := by
  apply nodeValid_prime [2, 5, 61, 662861359] ⟨6469526863841, 3, [(2, 5), (5, 1), (61, 1), (662861359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_662861359
  · decide +kernel

theorem prime_6469526913659 : Nat.Prime 6469526913659 := by
  apply nodeValid_prime [2, 157, 2647, 7783751] ⟨6469526913659, 2, [(2, 1), (157, 1), (2647, 1), (7783751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_2647
    · exact prime_7783751
  · decide +kernel

theorem prime_6469526913901 : Nat.Prime 6469526913901 := by
  apply nodeValid_prime [2, 3, 5, 17, 797, 1591637] ⟨6469526913901, 2, [(2, 2), (3, 1), (5, 2), (17, 1), (797, 1), (1591637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_797
    · exact prime_1591637
  · decide +kernel

theorem prime_6474143565559 : Nat.Prime 6474143565559 := by
  apply nodeValid_prime [2, 3, 359674642531] ⟨6474143565559, 6, [(2, 1), (3, 2), (359674642531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359674642531
  · decide +kernel

theorem prime_6474143587267 : Nat.Prime 6474143587267 := by
  apply nodeValid_prime [2, 3, 113, 449, 7089001] ⟨6474143587267, 2, [(2, 1), (3, 2), (113, 1), (449, 1), (7089001, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_113
    · exact prime_449
    · exact prime_7089001
  · decide +kernel

theorem prime_6474143587433 : Nat.Prime 6474143587433 := by
  apply nodeValid_prime [2, 137, 3967, 1489051] ⟨6474143587433, 3, [(2, 3), (137, 1), (3967, 1), (1489051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_3967
    · exact prime_1489051
  · decide +kernel

theorem prime_6478762496021 : Nat.Prime 6478762496021 := by
  apply nodeValid_prime [2, 5, 859, 377110739] ⟨6478762496021, 2, [(2, 2), (5, 1), (859, 1), (377110739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_859
    · exact prime_377110739
  · decide +kernel

theorem prime_6478762512119 : Nat.Prime 6478762512119 := by
  apply nodeValid_prime [2, 13, 11969, 20819047] ⟨6478762512119, 7, [(2, 1), (13, 1), (11969, 1), (20819047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_11969
    · exact prime_20819047
  · decide +kernel

theorem prime_6478762512683 : Nat.Prime 6478762512683 := by
  apply nodeValid_prime [2, 761, 4256742781] ⟨6478762512683, 2, [(2, 1), (761, 1), (4256742781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_761
    · exact prime_4256742781
  · decide +kernel

theorem prime_6483383634857 : Nat.Prime 6483383634857 := by
  apply nodeValid_prime [2, 19, 31, 1051, 1309163] ⟨6483383634857, 3, [(2, 3), (19, 1), (31, 1), (1051, 1), (1309163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_31
    · exact prime_1051
    · exact prime_1309163
  · decide +kernel

theorem prime_6483383656133 : Nat.Prime 6483383656133 := by
  apply nodeValid_prime [2, 1907, 4483, 189593] ⟨6483383656133, 2, [(2, 2), (1907, 1), (4483, 1), (189593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1907
    · exact prime_4483
    · exact prime_189593
  · decide +kernel

theorem prime_6488007038479 : Nat.Prime 6488007038479 := by
  apply nodeValid_prime [2, 3, 7, 571, 90178843] ⟨6488007038479, 6, [(2, 1), (3, 2), (7, 1), (571, 1), (90178843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_571
    · exact prime_90178843
  · decide +kernel

theorem prime_6488007092821 : Nat.Prime 6488007092821 := by
  apply nodeValid_prime [2, 3, 5, 11, 97, 33781147] ⟨6488007092821, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (97, 1), (33781147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_97
    · exact prime_33781147
  · decide +kernel

theorem prime_6488007095677 : Nat.Prime 6488007095677 := by
  apply nodeValid_prime [2, 3, 929, 2543, 228859] ⟨6488007095677, 6, [(2, 2), (3, 1), (929, 1), (2543, 1), (228859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
    · exact prime_2543
    · exact prime_228859
  · decide +kernel

theorem prime_6492632645353 : Nat.Prime 6492632645353 := by
  apply nodeValid_prime [2, 3, 7, 67, 73, 239, 4723] ⟨6492632645353, 10, [(2, 3), (3, 1), (7, 2), (67, 1), (73, 1), (239, 1), (4723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
    · exact prime_73
    · exact prime_239
    · exact prime_4723
  · decide +kernel

theorem prime_6492632786707 : Nat.Prime 6492632786707 := by
  apply nodeValid_prime [2, 3, 11, 98373224041] ⟨6492632786707, 5, [(2, 1), (3, 1), (11, 1), (98373224041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_98373224041
  · decide +kernel

theorem prime_6492632786779 : Nat.Prime 6492632786779 := by
  apply nodeValid_prime [2, 3, 23333, 46376611] ⟨6492632786779, 3, [(2, 1), (3, 1), (23333, 1), (46376611, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23333
    · exact prime_46376611
  · decide +kernel

theorem prime_6497260460281 : Nat.Prime 6497260460281 := by
  apply nodeValid_prime [2, 3, 5, 89, 202785907] ⟨6497260460281, 7, [(2, 3), (3, 2), (5, 1), (89, 1), (202785907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_89
    · exact prime_202785907
  · decide +kernel

theorem prime_6497260460347 : Nat.Prime 6497260460347 := by
  apply nodeValid_prime [2, 3, 631, 1877, 914293] ⟨6497260460347, 3, [(2, 1), (3, 1), (631, 1), (1877, 1), (914293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
    · exact prime_1877
    · exact prime_914293
  · decide +kernel

theorem prime_6497260480427 : Nat.Prime 6497260480427 := by
  apply nodeValid_prime [2, 173, 33857, 554633] ⟨6497260480427, 2, [(2, 1), (173, 1), (33857, 1), (554633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_173
    · exact prime_33857
    · exact prime_554633
  · decide +kernel

theorem prime_6501890490731 : Nat.Prime 6501890490731 := by
  apply nodeValid_prime [2, 5, 19, 29, 1180016423] ⟨6501890490731, 2, [(2, 1), (5, 1), (19, 1), (29, 1), (1180016423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_29
    · exact prime_1180016423
  · decide +kernel

theorem prime_6501890491969 : Nat.Prime 6501890491969 := by
  apply nodeValid_prime [2, 3, 33864012979] ⟨6501890491969, 7, [(2, 6), (3, 1), (33864012979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_33864012979
  · decide +kernel

theorem prime_6501890528537 : Nat.Prime 6501890528537 := by
  apply nodeValid_prime [2, 13, 62518178159] ⟨6501890528537, 3, [(2, 3), (13, 1), (62518178159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_62518178159
  · decide +kernel

theorem prime_6506522811077 : Nat.Prime 6506522811077 := by
  apply nodeValid_prime [2, 19, 2203, 5987, 6491] ⟨6506522811077, 2, [(2, 2), (19, 1), (2203, 1), (5987, 1), (6491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2203
    · exact prime_5987
    · exact prime_6491
  · decide +kernel

theorem prime_6506523015101 : Nat.Prime 6506523015101 := by
  apply nodeValid_prime [2, 5, 269, 379, 638201] ⟨6506523015101, 3, [(2, 2), (5, 2), (269, 1), (379, 1), (638201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_379
    · exact prime_638201
  · decide +kernel

theorem prime_6506523015361 : Nat.Prime 6506523015361 := by
  apply nodeValid_prime [2, 3, 5, 6777628141] ⟨6506523015361, 29, [(2, 6), (3, 1), (5, 1), (6777628141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6777628141
  · decide +kernel

theorem prime_6511157299363 : Nat.Prime 6511157299363 := by
  apply nodeValid_prime [2, 3, 431, 29473, 85429] ⟨6511157299363, 2, [(2, 1), (3, 1), (431, 1), (29473, 1), (85429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
    · exact prime_29473
    · exact prime_85429
  · decide +kernel

theorem prime_6511157300309 : Nat.Prime 6511157300309 := by
  apply nodeValid_prime [2, 31, 148667, 353201] ⟨6511157300309, 2, [(2, 2), (31, 1), (148667, 1), (353201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_148667
    · exact prime_353201
  · decide +kernel

theorem prime_6511157344847 : Nat.Prime 6511157344847 := by
  apply nodeValid_prime [2, 7, 11, 19, 23, 8795557] ⟨6511157344847, 5, [(2, 1), (7, 1), (11, 2), (19, 1), (23, 1), (8795557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_23
    · exact prime_8795557
  · decide +kernel

theorem prime_6515794116833 : Nat.Prime 6515794116833 := by
  apply nodeValid_prime [2, 7, 11, 13, 23, 1987, 4451] ⟨6515794116833, 3, [(2, 5), (7, 1), (11, 1), (13, 1), (23, 1), (1987, 1), (4451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_23
    · exact prime_1987
    · exact prime_4451
  · decide +kernel

theorem prime_6515794244251 : Nat.Prime 6515794244251 := by
  apply nodeValid_prime [2, 3, 5, 367, 876751] ⟨6515794244251, 13, [(2, 1), (3, 4), (5, 3), (367, 1), (876751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_367
    · exact prime_876751
  · decide +kernel

theorem prime_6520433074187 : Nat.Prime 6520433074187 := by
  apply nodeValid_prime [2, 23, 141748545091] ⟨6520433074187, 2, [(2, 1), (23, 1), (141748545091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_141748545091
  · decide +kernel

theorem prime_6520433074481 : Nat.Prime 6520433074481 := by
  apply nodeValid_prime [2, 5, 13, 33623, 186469] ⟨6520433074481, 3, [(2, 4), (5, 1), (13, 1), (33623, 1), (186469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_33623
    · exact prime_186469
  · decide +kernel

theorem prime_6520433127217 : Nat.Prime 6520433127217 := by
  apply nodeValid_prime [2, 3, 47, 2890262911] ⟨6520433127217, 5, [(2, 4), (3, 1), (47, 1), (2890262911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_2890262911
  · decide +kernel

theorem prime_6525074372987 : Nat.Prime 6525074372987 := by
  apply nodeValid_prime [2, 13, 23, 47, 509, 456109] ⟨6525074372987, 5, [(2, 1), (13, 1), (23, 1), (47, 1), (509, 1), (456109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
    · exact prime_47
    · exact prime_509
    · exact prime_456109
  · decide +kernel

theorem prime_6525074427847 : Nat.Prime 6525074427847 := by
  apply nodeValid_prime [2, 3, 13, 31, 14779, 182593] ⟨6525074427847, 17, [(2, 1), (3, 1), (13, 1), (31, 1), (14779, 1), (182593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_14779
    · exact prime_182593
  · decide +kernel

theorem prime_6525074428567 : Nat.Prime 6525074428567 := by
  apply nodeValid_prime [2, 3, 349, 1063, 1249, 2347] ⟨6525074428567, 5, [(2, 1), (3, 1), (349, 1), (1063, 1), (1249, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_349
    · exact prime_1063
    · exact prime_1249
    · exact prime_2347
  · decide +kernel

theorem prime_6529717856657 : Nat.Prime 6529717856657 := by
  apply nodeValid_prime [2, 71, 1597, 3599243] ⟨6529717856657, 3, [(2, 4), (71, 1), (1597, 1), (3599243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1597
    · exact prime_3599243
  · decide +kernel

theorem prime_6529717884367 : Nat.Prime 6529717884367 := by
  apply nodeValid_prime [2, 3, 31, 23143, 505639] ⟨6529717884367, 5, [(2, 1), (3, 2), (31, 1), (23143, 1), (505639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_23143
    · exact prime_505639
  · decide +kernel

theorem prime_6529717885759 : Nat.Prime 6529717885759 := by
  apply nodeValid_prime [2, 3, 1088286314293] ⟨6529717885759, 3, [(2, 1), (3, 1), (1088286314293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1088286314293
  · decide +kernel

theorem prime_6534363574367 : Nat.Prime 6534363574367 := by
  apply nodeValid_prime [2, 41, 5099, 15628037] ⟨6534363574367, 5, [(2, 1), (41, 1), (5099, 1), (15628037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_5099
    · exact prime_15628037
  · decide +kernel

theorem prime_6534363591037 : Nat.Prime 6534363591037 := by
  apply nodeValid_prime [2, 3, 379, 478918469] ⟨6534363591037, 2, [(2, 2), (3, 2), (379, 1), (478918469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_379
    · exact prime_478918469
  · decide +kernel

theorem prime_6534363591127 : Nat.Prime 6534363591127 := by
  apply nodeValid_prime [2, 3, 7, 5762225389] ⟨6534363591127, 3, [(2, 1), (3, 4), (7, 1), (5762225389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_5762225389
  · decide +kernel

theorem prime_6539011452011 : Nat.Prime 6539011452011 := by
  apply nodeValid_prime [2, 5, 731267, 894203] ⟨6539011452011, 6, [(2, 1), (5, 1), (731267, 1), (894203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_731267
    · exact prime_894203
  · decide +kernel

theorem prime_6539011454981 : Nat.Prime 6539011454981 := by
  apply nodeValid_prime [2, 5, 29, 89, 9239, 13711] ⟨6539011454981, 2, [(2, 2), (5, 1), (29, 1), (89, 1), (9239, 1), (13711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_89
    · exact prime_9239
    · exact prime_13711
  · decide +kernel

theorem prime_6539011533869 : Nat.Prime 6539011533869 := by
  apply nodeValid_prime [2, 11, 179, 830245243] ⟨6539011533869, 2, [(2, 2), (11, 1), (179, 1), (830245243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_179
    · exact prime_830245243
  · decide +kernel

theorem prime_6543661552819 : Nat.Prime 6543661552819 := by
  apply nodeValid_prime [2, 3, 13, 19, 4415426149] ⟨6543661552819, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (4415426149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_4415426149
  · decide +kernel

theorem prime_6543661553291 : Nat.Prime 6543661553291 := by
  apply nodeValid_prime [2, 5, 311, 1709, 1231171] ⟨6543661553291, 2, [(2, 1), (5, 1), (311, 1), (1709, 1), (1231171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_311
    · exact prime_1709
    · exact prime_1231171
  · decide +kernel

theorem prime_6543661737911 : Nat.Prime 6543661737911 := by
  apply nodeValid_prime [2, 5, 11, 89, 668402629] ⟨6543661737911, 17, [(2, 1), (5, 1), (11, 1), (89, 1), (668402629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_89
    · exact prime_668402629
  · decide +kernel

theorem prime_6548314169993 : Nat.Prime 6548314169993 := by
  apply nodeValid_prime [2, 7, 17, 22817, 301463] ⟨6548314169993, 3, [(2, 3), (7, 1), (17, 1), (22817, 1), (301463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_22817
    · exact prime_301463
  · decide +kernel

theorem prime_6548314207159 : Nat.Prime 6548314207159 := by
  apply nodeValid_prime [2, 3, 363795233731] ⟨6548314207159, 6, [(2, 1), (3, 2), (363795233731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_363795233731
  · decide +kernel

theorem prime_6548314207283 : Nat.Prime 6548314207283 := by
  apply nodeValid_prime [2, 3274157103641] ⟨6548314207283, 2, [(2, 1), (3274157103641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3274157103641
  · decide +kernel

theorem prime_6552968761037 : Nat.Prime 6552968761037 := by
  apply nodeValid_prime [2, 40853, 40100903] ⟨6552968761037, 2, [(2, 2), (40853, 1), (40100903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_40853
    · exact prime_40100903
  · decide +kernel

theorem prime_6552968762387 : Nat.Prime 6552968762387 := by
  apply nodeValid_prime [2, 181, 401, 45142453] ⟨6552968762387, 2, [(2, 1), (181, 1), (401, 1), (45142453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_401
    · exact prime_45142453
  · decide +kernel

theorem prime_6552968847683 : Nat.Prime 6552968847683 := by
  apply nodeValid_prime [2, 17, 953, 4517, 44773] ⟨6552968847683, 2, [(2, 1), (17, 1), (953, 1), (4517, 1), (44773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_953
    · exact prime_4517
    · exact prime_44773
  · decide +kernel

end Sude.Lucas.Generated
