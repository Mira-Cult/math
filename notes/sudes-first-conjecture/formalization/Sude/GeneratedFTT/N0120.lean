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
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0046
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0052
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0057
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0070
import Sude.GeneratedFTT.N0072
import Sude.GeneratedFTT.N0074
import Sude.GeneratedFTT.N0075
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0080
import Sude.GeneratedFTT.N0089
import Sude.GeneratedFTT.N0096
import Sude.GeneratedFTT.N0101
import Sude.GeneratedFTT.N0114
import Sude.GeneratedFTT.N0116
import Sude.GeneratedFTT.N0119

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_5059 : Nat.Prime 5059 := by
  apply nodeValid_prime [2, 3, 281] ⟨5059, 2, [(2, 1), (3, 2), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
  · decide +kernel

theorem prime_21031 : Nat.Prime 21031 := by
  apply nodeValid_prime [2, 3, 5, 701] ⟨21031, 12, [(2, 1), (3, 1), (5, 1), (701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_701
  · decide +kernel

theorem prime_30139 : Nat.Prime 30139 := by
  apply nodeValid_prime [2, 3, 5023] ⟨30139, 2, [(2, 1), (3, 1), (5023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5023
  · decide +kernel

theorem prime_33589 : Nat.Prime 33589 := by
  apply nodeValid_prime [2, 3, 311] ⟨33589, 2, [(2, 2), (3, 3), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
  · decide +kernel

theorem prime_41627 : Nat.Prime 41627 := by
  apply nodeValid_prime [2, 13, 1601] ⟨41627, 2, [(2, 1), (13, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1601
  · decide +kernel

theorem prime_41893 : Nat.Prime 41893 := by
  apply nodeValid_prime [2, 3, 3491] ⟨41893, 2, [(2, 2), (3, 1), (3491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3491
  · decide +kernel

theorem prime_42767 : Nat.Prime 42767 := by
  apply nodeValid_prime [2, 21383] ⟨42767, 5, [(2, 1), (21383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21383
  · decide +kernel

theorem prime_58537 : Nat.Prime 58537 := by
  apply nodeValid_prime [2, 3, 271] ⟨58537, 7, [(2, 3), (3, 3), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
  · decide +kernel

theorem prime_59399 : Nat.Prime 59399 := by
  apply nodeValid_prime [2, 17, 1747] ⟨59399, 7, [(2, 1), (17, 1), (1747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1747
  · decide +kernel

theorem prime_62753 : Nat.Prime 62753 := by
  apply nodeValid_prime [2, 37, 53] ⟨62753, 3, [(2, 5), (37, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_53
  · decide +kernel

theorem prime_64579 : Nat.Prime 64579 := by
  apply nodeValid_prime [2, 3, 47, 229] ⟨64579, 2, [(2, 1), (3, 1), (47, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_229
  · decide +kernel

theorem prime_68743 : Nat.Prime 68743 := by
  apply nodeValid_prime [2, 3, 19, 67] ⟨68743, 3, [(2, 1), (3, 3), (19, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_67
  · decide +kernel

theorem prime_74077 : Nat.Prime 74077 := by
  apply nodeValid_prime [2, 3, 6173] ⟨74077, 5, [(2, 2), (3, 1), (6173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6173
  · decide +kernel

theorem prime_75017 : Nat.Prime 75017 := by
  apply nodeValid_prime [2, 9377] ⟨75017, 3, [(2, 3), (9377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9377
  · decide +kernel

theorem prime_80141 : Nat.Prime 80141 := by
  apply nodeValid_prime [2, 5, 4007] ⟨80141, 2, [(2, 2), (5, 1), (4007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4007
  · decide +kernel

theorem prime_84697 : Nat.Prime 84697 := by
  apply nodeValid_prime [2, 3, 3529] ⟨84697, 11, [(2, 3), (3, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3529
  · decide +kernel

theorem prime_84967 : Nat.Prime 84967 := by
  apply nodeValid_prime [2, 3, 7, 17] ⟨84967, 3, [(2, 1), (3, 1), (7, 2), (17, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
  · decide +kernel

theorem prime_85991 : Nat.Prime 85991 := by
  apply nodeValid_prime [2, 5, 8599] ⟨85991, 11, [(2, 1), (5, 1), (8599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_8599
  · decide +kernel

theorem prime_91397 : Nat.Prime 91397 := by
  apply nodeValid_prime [2, 73, 313] ⟨91397, 2, [(2, 2), (73, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_313
  · decide +kernel

theorem prime_95857 : Nat.Prime 95857 := by
  apply nodeValid_prime [2, 3, 1997] ⟨95857, 10, [(2, 4), (3, 1), (1997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1997
  · decide +kernel

theorem prime_112657 : Nat.Prime 112657 := by
  apply nodeValid_prime [2, 3, 2347] ⟨112657, 7, [(2, 4), (3, 1), (2347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2347
  · decide +kernel

theorem prime_113279 : Nat.Prime 113279 := by
  apply nodeValid_prime [2, 11, 19, 271] ⟨113279, 11, [(2, 1), (11, 1), (19, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_271
  · decide +kernel

theorem prime_117307 : Nat.Prime 117307 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨117307, 5, [(2, 1), (3, 2), (7, 3), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_125507 : Nat.Prime 125507 := by
  apply nodeValid_prime [2, 62753] ⟨125507, 2, [(2, 1), (62753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_62753
  · decide +kernel

theorem prime_134741 : Nat.Prime 134741 := by
  apply nodeValid_prime [2, 5, 6737] ⟨134741, 2, [(2, 2), (5, 1), (6737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6737
  · decide +kernel

theorem prime_160483 : Nat.Prime 160483 := by
  apply nodeValid_prime [2, 3, 7, 3821] ⟨160483, 3, [(2, 1), (3, 1), (7, 1), (3821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3821
  · decide +kernel

theorem prime_161569 : Nat.Prime 161569 := by
  apply nodeValid_prime [2, 3, 11, 17] ⟨161569, 13, [(2, 5), (3, 3), (11, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
  · decide +kernel

theorem prime_171251 : Nat.Prime 171251 := by
  apply nodeValid_prime [2, 5, 137] ⟨171251, 2, [(2, 1), (5, 4), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_180793 : Nat.Prime 180793 := by
  apply nodeValid_prime [2, 3, 31] ⟨180793, 10, [(2, 3), (3, 6), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_213287 : Nat.Prime 213287 := by
  apply nodeValid_prime [2, 47, 2269] ⟨213287, 5, [(2, 1), (47, 1), (2269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_2269
  · decide +kernel

theorem prime_217027 : Nat.Prime 217027 := by
  apply nodeValid_prime [2, 3, 4019] ⟨217027, 2, [(2, 1), (3, 3), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4019
  · decide +kernel

theorem prime_224729 : Nat.Prime 224729 := by
  apply nodeValid_prime [2, 7, 4013] ⟨224729, 3, [(2, 3), (7, 1), (4013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4013
  · decide +kernel

theorem prime_274973 : Nat.Prime 274973 := by
  apply nodeValid_prime [2, 68743] ⟨274973, 2, [(2, 2), (68743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_68743
  · decide +kernel

theorem prime_304751 : Nat.Prime 304751 := by
  apply nodeValid_prime [2, 5, 23, 53] ⟨304751, 13, [(2, 1), (5, 3), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_309011 : Nat.Prime 309011 := by
  apply nodeValid_prime [2, 5, 13, 2377] ⟨309011, 2, [(2, 1), (5, 1), (13, 1), (2377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_2377
  · decide +kernel

theorem prime_351223 : Nat.Prime 351223 := by
  apply nodeValid_prime [2, 3, 58537] ⟨351223, 3, [(2, 1), (3, 1), (58537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_58537
  · decide +kernel

theorem prime_383429 : Nat.Prime 383429 := by
  apply nodeValid_prime [2, 95857] ⟨383429, 2, [(2, 2), (95857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_95857
  · decide +kernel

theorem prime_439349 : Nat.Prime 439349 := by
  apply nodeValid_prime [2, 7, 13, 17, 71] ⟨439349, 2, [(2, 2), (7, 1), (13, 1), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_439961 : Nat.Prime 439961 := by
  apply nodeValid_prime [2, 5, 17, 647] ⟨439961, 3, [(2, 3), (5, 1), (17, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_647
  · decide +kernel

theorem prime_469229 : Nat.Prime 469229 := by
  apply nodeValid_prime [2, 117307] ⟨469229, 2, [(2, 2), (117307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_117307
  · decide +kernel

theorem prime_509843 : Nat.Prime 509843 := by
  apply nodeValid_prime [2, 227, 1123] ⟨509843, 2, [(2, 1), (227, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_1123
  · decide +kernel

theorem prime_581473 : Nat.Prime 581473 := by
  apply nodeValid_prime [2, 3, 673] ⟨581473, 5, [(2, 5), (3, 3), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_673
  · decide +kernel

theorem prime_602377 : Nat.Prime 602377 := by
  apply nodeValid_prime [2, 3, 19, 1321] ⟨602377, 7, [(2, 3), (3, 1), (19, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_1321
  · decide +kernel

theorem prime_723337 : Nat.Prime 723337 := by
  apply nodeValid_prime [2, 3, 30139] ⟨723337, 7, [(2, 3), (3, 1), (30139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_30139
  · decide +kernel

theorem prime_831587 : Nat.Prime 831587 := by
  apply nodeValid_prime [2, 7, 59399] ⟨831587, 2, [(2, 1), (7, 1), (59399, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59399
  · decide +kernel

theorem prime_938459 : Nat.Prime 938459 := by
  apply nodeValid_prime [2, 469229] ⟨938459, 2, [(2, 1), (469229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_469229
  · decide +kernel

theorem prime_1024327 : Nat.Prime 1024327 := by
  apply nodeValid_prime [2, 3, 6323] ⟨1024327, 3, [(2, 1), (3, 4), (6323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6323
  · decide +kernel

theorem prime_1162423 : Nat.Prime 1162423 := by
  apply nodeValid_prime [2, 3, 64579] ⟨1162423, 3, [(2, 1), (3, 2), (64579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_64579
  · decide +kernel

theorem prime_1201141 : Nat.Prime 1201141 := by
  apply nodeValid_prime [2, 3, 5, 6673] ⟨1201141, 6, [(2, 2), (3, 2), (5, 1), (6673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6673
  · decide +kernel

theorem prime_1355153 : Nat.Prime 1355153 := by
  apply nodeValid_prime [2, 84697] ⟨1355153, 3, [(2, 4), (84697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84697
  · decide +kernel

theorem prime_1500341 : Nat.Prime 1500341 := by
  apply nodeValid_prime [2, 5, 75017] ⟨1500341, 2, [(2, 2), (5, 1), (75017, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_75017
  · decide +kernel

theorem prime_2379077 : Nat.Prime 2379077 := by
  apply nodeValid_prime [2, 7, 84967] ⟨2379077, 2, [(2, 2), (7, 1), (84967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_84967
  · decide +kernel

theorem prime_2567729 : Nat.Prime 2567729 := by
  apply nodeValid_prime [2, 160483] ⟨2567729, 3, [(2, 4), (160483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_160483
  · decide +kernel

theorem prime_3019801 : Nat.Prime 3019801 := by
  apply nodeValid_prime [2, 3, 5, 7, 719] ⟨3019801, 13, [(2, 3), (3, 1), (5, 2), (7, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_719
  · decide +kernel

theorem prime_3173039 : Nat.Prime 3173039 := by
  apply nodeValid_prime [2, 11, 19, 7591] ⟨3173039, 7, [(2, 1), (11, 1), (19, 1), (7591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_7591
  · decide +kernel

theorem prime_3414413 : Nat.Prime 3414413 := by
  apply nodeValid_prime [2, 151, 5653] ⟨3414413, 2, [(2, 2), (151, 1), (5653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_5653
  · decide +kernel

theorem prime_3614263 : Nat.Prime 3614263 := by
  apply nodeValid_prime [2, 3, 602377] ⟨3614263, 3, [(2, 1), (3, 1), (602377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_602377
  · decide +kernel

theorem prime_3871271 : Nat.Prime 3871271 := by
  apply nodeValid_prime [2, 5, 13, 97, 307] ⟨3871271, 17, [(2, 1), (5, 1), (13, 1), (97, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_97
    · exact prime_307
  · decide +kernel

theorem prime_4006591 : Nat.Prime 4006591 := by
  apply nodeValid_prime [2, 3, 5, 7, 19079] ⟨4006591, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (19079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_19079
  · decide +kernel

theorem prime_4326121 : Nat.Prime 4326121 := by
  apply nodeValid_prime [2, 3, 5, 61, 197] ⟨4326121, 13, [(2, 3), (3, 2), (5, 1), (61, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
    · exact prime_197
  · decide +kernel

theorem prime_4984277 : Nat.Prime 4984277 := by
  apply nodeValid_prime [2, 11, 113279] ⟨4984277, 2, [(2, 2), (11, 1), (113279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_113279
  · decide +kernel

theorem prime_6508549 : Nat.Prime 6508549 := by
  apply nodeValid_prime [2, 3, 180793] ⟨6508549, 2, [(2, 2), (3, 2), (180793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_180793
  · decide +kernel

theorem prime_6785899 : Nat.Prime 6785899 := by
  apply nodeValid_prime [2, 3, 7, 161569] ⟨6785899, 2, [(2, 1), (3, 1), (7, 1), (161569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_161569
  · decide +kernel

theorem prime_7798811 : Nat.Prime 7798811 := by
  apply nodeValid_prime [2, 5, 199, 3919] ⟨7798811, 2, [(2, 1), (5, 1), (199, 1), (3919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_199
    · exact prime_3919
  · decide +kernel

theorem prime_8322773 : Nat.Prime 8322773 := by
  apply nodeValid_prime [2, 863, 2411] ⟨8322773, 2, [(2, 2), (863, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_863
    · exact prime_2411
  · decide +kernel

theorem prime_8670743 : Nat.Prime 8670743 := by
  apply nodeValid_prime [2, 367, 11813] ⟨8670743, 5, [(2, 1), (367, 1), (11813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_11813
  · decide +kernel

theorem prime_8732411 : Nat.Prime 8732411 := by
  apply nodeValid_prime [2, 5, 23, 37967] ⟨8732411, 2, [(2, 1), (5, 1), (23, 1), (37967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_37967
  · decide +kernel

theorem prime_9138133 : Nat.Prime 9138133 := by
  apply nodeValid_prime [2, 3, 29, 8753] ⟨9138133, 2, [(2, 2), (3, 2), (29, 1), (8753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_8753
  · decide +kernel

theorem prime_9925931 : Nat.Prime 9925931 := by
  apply nodeValid_prime [2, 5, 7, 47, 431] ⟨9925931, 2, [(2, 1), (5, 1), (7, 2), (47, 1), (431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_47
    · exact prime_431
  · decide +kernel

theorem prime_14552029 : Nat.Prime 14552029 := by
  apply nodeValid_prime [2, 3, 134741] ⟨14552029, 2, [(2, 2), (3, 3), (134741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_134741
  · decide +kernel

theorem prime_14676979 : Nat.Prime 14676979 := by
  apply nodeValid_prime [2, 3, 71, 131, 263] ⟨14676979, 2, [(2, 1), (3, 1), (71, 1), (131, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_131
    · exact prime_263
  · decide +kernel

theorem prime_17540357 : Nat.Prime 17540357 := by
  apply nodeValid_prime [2, 751, 5839] ⟨17540357, 2, [(2, 2), (751, 1), (5839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_751
    · exact prime_5839
  · decide +kernel

theorem prime_24306259 : Nat.Prime 24306259 := by
  apply nodeValid_prime [2, 3, 199, 20357] ⟨24306259, 3, [(2, 1), (3, 1), (199, 1), (20357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_20357
  · decide +kernel

theorem prime_25677109 : Nat.Prime 25677109 := by
  apply nodeValid_prime [2, 3, 23, 10337] ⟨25677109, 2, [(2, 2), (3, 3), (23, 1), (10337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_10337
  · decide +kernel

theorem prime_28702697 : Nat.Prime 28702697 := by
  apply nodeValid_prime [2, 11, 61, 5347] ⟨28702697, 3, [(2, 3), (11, 1), (61, 1), (5347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_5347
  · decide +kernel

theorem prime_28999447 : Nat.Prime 28999447 := by
  apply nodeValid_prime [2, 3, 7, 31, 22273] ⟨28999447, 3, [(2, 1), (3, 1), (7, 1), (31, 1), (22273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_22273
  · decide +kernel

theorem prime_30970169 : Nat.Prime 30970169 := by
  apply nodeValid_prime [2, 3871271] ⟨30970169, 3, [(2, 3), (3871271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3871271
  · decide +kernel

theorem prime_33418669 : Nat.Prime 33418669 := by
  apply nodeValid_prime [2, 3, 17, 107, 1531] ⟨33418669, 6, [(2, 2), (3, 1), (17, 1), (107, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_107
    · exact prime_1531
  · decide +kernel

theorem prime_40065911 : Nat.Prime 40065911 := by
  apply nodeValid_prime [2, 5, 4006591] ⟨40065911, 7, [(2, 1), (5, 1), (4006591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_4006591
  · decide +kernel

theorem prime_40078111 : Nat.Prime 40078111 := by
  apply nodeValid_prime [2, 3, 5, 59, 22643] ⟨40078111, 3, [(2, 1), (3, 1), (5, 1), (59, 1), (22643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_22643
  · decide +kernel

theorem prime_42066581 : Nat.Prime 42066581 := by
  apply nodeValid_prime [2, 5, 157, 13397] ⟨42066581, 2, [(2, 2), (5, 1), (157, 1), (13397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
    · exact prime_13397
  · decide +kernel

theorem prime_52394467 : Nat.Prime 52394467 := by
  apply nodeValid_prime [2, 3, 8732411] ⟨52394467, 2, [(2, 1), (3, 1), (8732411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8732411
  · decide +kernel

theorem prime_61459621 : Nat.Prime 61459621 := by
  apply nodeValid_prime [2, 3, 5, 1024327] ⟨61459621, 7, [(2, 2), (3, 1), (5, 1), (1024327, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1024327
  · decide +kernel

theorem prime_67858991 : Nat.Prime 67858991 := by
  apply nodeValid_prime [2, 5, 6785899] ⟨67858991, 13, [(2, 1), (5, 1), (6785899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6785899
  · decide +kernel

theorem prime_110440633 : Nat.Prime 110440633 := by
  apply nodeValid_prime [2, 3, 137, 33589] ⟨110440633, 5, [(2, 3), (3, 1), (137, 1), (33589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_33589
  · decide +kernel

theorem prime_129253643 : Nat.Prime 129253643 := by
  apply nodeValid_prime [2, 7, 359, 25717] ⟨129253643, 2, [(2, 1), (7, 1), (359, 1), (25717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_359
    · exact prime_25717
  · decide +kernel

theorem prime_137980207 : Nat.Prime 137980207 := by
  apply nodeValid_prime [2, 3, 7, 13, 43, 653] ⟨137980207, 3, [(2, 1), (3, 3), (7, 1), (13, 1), (43, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_43
    · exact prime_653
  · decide +kernel

theorem prime_158651951 : Nat.Prime 158651951 := by
  apply nodeValid_prime [2, 5, 3173039] ⟨158651951, 17, [(2, 1), (5, 2), (3173039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3173039
  · decide +kernel

theorem prime_222095651 : Nat.Prime 222095651 := by
  apply nodeValid_prime [2, 5, 7, 17, 163, 229] ⟨222095651, 6, [(2, 1), (5, 2), (7, 1), (17, 1), (163, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_163
    · exact prime_229
  · decide +kernel

theorem prime_322893539 : Nat.Prime 322893539 := by
  apply nodeValid_prime [2, 11, 14676979] ⟨322893539, 2, [(2, 1), (11, 1), (14676979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_14676979
  · decide +kernel

theorem prime_372459011 : Nat.Prime 372459011 := by
  apply nodeValid_prime [2, 5, 7, 11, 23, 21031] ⟨372459011, 2, [(2, 1), (5, 1), (7, 1), (11, 1), (23, 1), (21031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_21031
  · decide +kernel

theorem prime_393397523 : Nat.Prime 393397523 := by
  apply nodeValid_prime [2, 7, 113, 139, 1789] ⟨393397523, 2, [(2, 1), (7, 1), (113, 1), (139, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_113
    · exact prime_139
    · exact prime_1789
  · decide +kernel

theorem prime_410692937 : Nat.Prime 410692937 := by
  apply nodeValid_prime [2, 17, 3019801] ⟨410692937, 3, [(2, 3), (17, 1), (3019801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3019801
  · decide +kernel

theorem prime_418259713 : Nat.Prime 418259713 := by
  apply nodeValid_prime [2, 3, 13, 41893] ⟨418259713, 5, [(2, 8), (3, 1), (13, 1), (41893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_41893
  · decide +kernel

theorem prime_444191303 : Nat.Prime 444191303 := by
  apply nodeValid_prime [2, 222095651] ⟨444191303, 5, [(2, 1), (222095651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_222095651
  · decide +kernel

theorem prime_943100407 : Nat.Prime 943100407 := by
  apply nodeValid_prime [2, 3, 52394467] ⟨943100407, 3, [(2, 1), (3, 2), (52394467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_52394467
  · decide +kernel

theorem prime_1297614887 : Nat.Prime 1297614887 := by
  apply nodeValid_prime [2, 71, 9138133] ⟨1297614887, 5, [(2, 1), (71, 1), (9138133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_9138133
  · decide +kernel

theorem prime_2291712463 : Nat.Prime 2291712463 := by
  apply nodeValid_prime [2, 3, 13, 229, 42767] ⟨2291712463, 3, [(2, 1), (3, 2), (13, 1), (229, 1), (42767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_229
    · exact prime_42767
  · decide +kernel

theorem prime_2319762721 : Nat.Prime 2319762721 := by
  apply nodeValid_prime [2, 3, 5, 11, 439349] ⟨2319762721, 7, [(2, 5), (3, 1), (5, 1), (11, 1), (439349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_439349
  · decide +kernel

theorem prime_2442923677 : Nat.Prime 2442923677 := by
  apply nodeValid_prime [2, 3, 67858991] ⟨2442923677, 2, [(2, 2), (3, 2), (67858991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67858991
  · decide +kernel

theorem prime_2464157623 : Nat.Prime 2464157623 := by
  apply nodeValid_prime [2, 3, 410692937] ⟨2464157623, 5, [(2, 1), (3, 1), (410692937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_410692937
  · decide +kernel

theorem prime_2665147819 : Nat.Prime 2665147819 := by
  apply nodeValid_prime [2, 3, 444191303] ⟨2665147819, 2, [(2, 1), (3, 1), (444191303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_444191303
  · decide +kernel

theorem prime_2693377331 : Nat.Prime 2693377331 := by
  apply nodeValid_prime [2, 5, 7, 41, 938459] ⟨2693377331, 2, [(2, 1), (5, 1), (7, 1), (41, 1), (938459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_41
    · exact prime_938459
  · decide +kernel

theorem prime_2855735119 : Nat.Prime 2855735119 := by
  apply nodeValid_prime [2, 3, 158651951] ⟨2855735119, 3, [(2, 1), (3, 2), (158651951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_158651951
  · decide +kernel

theorem prime_4891076543 : Nat.Prime 4891076543 := by
  apply nodeValid_prime [2, 11, 71, 293, 10687] ⟨4891076543, 5, [(2, 1), (11, 1), (71, 1), (293, 1), (10687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_293
    · exact prime_10687
  · decide +kernel

theorem prime_5104885519 : Nat.Prime 5104885519 := by
  apply nodeValid_prime [2, 3, 757, 41627] ⟨5104885519, 3, [(2, 1), (3, 4), (757, 1), (41627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_757
    · exact prime_41627
  · decide +kernel

theorem prime_6198991313 : Nat.Prime 6198991313 := by
  apply nodeValid_prime [2, 1409, 274973] ⟨6198991313, 3, [(2, 4), (1409, 1), (274973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1409
    · exact prime_274973
  · decide +kernel

theorem prime_6250282117 : Nat.Prime 6250282117 := by
  apply nodeValid_prime [2, 3, 13, 40065911] ⟨6250282117, 2, [(2, 2), (3, 1), (13, 1), (40065911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_40065911
  · decide +kernel

theorem prime_8483788583 : Nat.Prime 8483788583 := by
  apply nodeValid_prime [2, 1783, 2379077] ⟨8483788583, 5, [(2, 1), (1783, 1), (2379077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1783
    · exact prime_2379077
  · decide +kernel

theorem prime_8687745023 : Nat.Prime 8687745023 := by
  apply nodeValid_prime [2, 11, 19, 1171, 17749] ⟨8687745023, 5, [(2, 1), (11, 1), (19, 1), (1171, 1), (17749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_1171
    · exact prime_17749
  · decide +kernel

theorem prime_12397982627 : Nat.Prime 12397982627 := by
  apply nodeValid_prime [2, 6198991313] ⟨12397982627, 2, [(2, 1), (6198991313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6198991313
  · decide +kernel

theorem prime_22142772811 : Nat.Prime 22142772811 := by
  apply nodeValid_prime [2, 3, 5, 29, 1301, 6521] ⟨22142772811, 3, [(2, 1), (3, 2), (5, 1), (29, 1), (1301, 1), (6521, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_1301
    · exact prime_6521
  · decide +kernel

theorem prime_25952297741 : Nat.Prime 25952297741 := by
  apply nodeValid_prime [2, 5, 1297614887] ⟨25952297741, 2, [(2, 2), (5, 1), (1297614887, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1297614887
  · decide +kernel

theorem prime_28216098199 : Nat.Prime 28216098199 := by
  apply nodeValid_prime [2, 3, 67, 7798811] ⟨28216098199, 7, [(2, 1), (3, 3), (67, 1), (7798811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_7798811
  · decide +kernel

theorem prime_36269209891 : Nat.Prime 36269209891 := by
  apply nodeValid_prime [2, 3, 5, 29, 211, 757] ⟨36269209891, 2, [(2, 1), (3, 3), (5, 1), (29, 2), (211, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_211
    · exact prime_757
  · decide +kernel

theorem prime_36667399409 : Nat.Prime 36667399409 := by
  apply nodeValid_prime [2, 2291712463] ⟨36667399409, 3, [(2, 4), (2291712463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2291712463
  · decide +kernel

theorem prime_39086778833 : Nat.Prime 39086778833 := by
  apply nodeValid_prime [2, 2442923677] ⟨39086778833, 3, [(2, 4), (2442923677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2442923677
  · decide +kernel

theorem prime_42291145997 : Nat.Prime 42291145997 := by
  apply nodeValid_prime [2, 11, 31, 197, 5077] ⟨42291145997, 2, [(2, 2), (11, 1), (31, 2), (197, 1), (5077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_197
    · exact prime_5077
  · decide +kernel

theorem prime_49287724567 : Nat.Prime 49287724567 := by
  apply nodeValid_prime [2, 3, 173, 641, 74077] ⟨49287724567, 5, [(2, 1), (3, 1), (173, 1), (641, 1), (74077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_641
    · exact prime_74077
  · decide +kernel

theorem prime_54211467707 : Nat.Prime 54211467707 := by
  apply nodeValid_prime [2, 11, 2464157623] ⟨54211467707, 2, [(2, 1), (11, 1), (2464157623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2464157623
  · decide +kernel

theorem prime_58950532117 : Nat.Prime 58950532117 := by
  apply nodeValid_prime [2, 3, 7, 33418669] ⟨58950532117, 6, [(2, 2), (3, 2), (7, 2), (33418669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_33418669
  · decide +kernel

theorem prime_64953356189 : Nat.Prime 64953356189 := by
  apply nodeValid_prime [2, 7, 2319762721] ⟨64953356189, 11, [(2, 2), (7, 1), (2319762721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2319762721
  · decide +kernel

theorem prime_85243894297 : Nat.Prime 85243894297 := by
  apply nodeValid_prime [2, 3, 11, 322893539] ⟨85243894297, 5, [(2, 3), (3, 1), (11, 1), (322893539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_322893539
  · decide +kernel

theorem prime_102283355981 : Nat.Prime 102283355981 := by
  apply nodeValid_prime [2, 5, 13, 393397523] ⟨102283355981, 2, [(2, 2), (5, 1), (13, 1), (393397523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_393397523
  · decide +kernel

theorem prime_223860645391 : Nat.Prime 223860645391 := by
  apply nodeValid_prime [2, 3, 5, 307, 24306259] ⟨223860645391, 3, [(2, 1), (3, 1), (5, 1), (307, 1), (24306259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_307
    · exact prime_24306259
  · decide +kernel

theorem prime_224559057871 : Nat.Prime 224559057871 := by
  apply nodeValid_prime [2, 3, 5, 7, 613, 581473] ⟨224559057871, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (613, 1), (581473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_613
    · exact prime_581473
  · decide +kernel

theorem prime_247207293497 : Nat.Prime 247207293497 := by
  apply nodeValid_prime [2, 19, 7237, 224729] ⟨247207293497, 3, [(2, 3), (19, 1), (7237, 1), (224729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_7237
    · exact prime_224729
  · decide +kernel

theorem prime_274034041201 : Nat.Prime 274034041201 := by
  apply nodeValid_prime [2, 3, 5, 191, 353, 1129] ⟨274034041201, 13, [(2, 4), (3, 2), (5, 2), (191, 1), (353, 1), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_191
    · exact prime_353
    · exact prime_1129
  · decide +kernel

theorem prime_487522005127 : Nat.Prime 487522005127 := by
  apply nodeValid_prime [2, 3, 13, 6250282117] ⟨487522005127, 5, [(2, 1), (3, 1), (13, 1), (6250282117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_6250282117
  · decide +kernel

theorem prime_610832778041 : Nat.Prime 610832778041 := by
  apply nodeValid_prime [2, 5, 41, 372459011] ⟨610832778041, 6, [(2, 3), (5, 1), (41, 1), (372459011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_372459011
  · decide +kernel

theorem prime_816353764277 : Nat.Prime 816353764277 := by
  apply nodeValid_prime [2, 31, 149, 223, 347, 571] ⟨816353764277, 11, [(2, 2), (31, 1), (149, 1), (223, 1), (347, 1), (571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_149
    · exact prime_223
    · exact prime_347
    · exact prime_571
  · decide +kernel

theorem prime_825949519103 : Nat.Prime 825949519103 := by
  apply nodeValid_prime [2, 41, 73, 137980207] ⟨825949519103, 5, [(2, 1), (41, 1), (73, 1), (137980207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_73
    · exact prime_137980207
  · decide +kernel

theorem prime_1218805012069 : Nat.Prime 1218805012069 := by
  apply nodeValid_prime [2, 3, 7, 193, 439, 171251] ⟨1218805012069, 13, [(2, 2), (3, 1), (7, 1), (193, 1), (439, 1), (171251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_193
    · exact prime_439
    · exact prime_171251
  · decide +kernel

theorem prime_1220711538913 : Nat.Prime 1220711538913 := by
  apply nodeValid_prime [2, 3, 10939, 1162423] ⟨1220711538913, 5, [(2, 5), (3, 1), (10939, 1), (1162423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10939
    · exact prime_1162423
  · decide +kernel

theorem prime_1221665555953 : Nat.Prime 1221665555953 := by
  apply nodeValid_prime [2, 3, 8483788583] ⟨1221665555953, 5, [(2, 4), (3, 2), (8483788583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8483788583
  · decide +kernel

theorem prime_2443331118821 : Nat.Prime 2443331118821 := by
  apply nodeValid_prime [2, 5, 168893, 723337] ⟨2443331118821, 2, [(2, 2), (5, 1), (168893, 1), (723337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_168893
    · exact prime_723337
  · decide +kernel

theorem prime_2452886458931 : Nat.Prime 2452886458931 := by
  apply nodeValid_prime [2, 5, 2221, 110440633] ⟨2452886458931, 2, [(2, 1), (5, 1), (2221, 1), (110440633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2221
    · exact prime_110440633
  · decide +kernel

theorem prime_2468227535183 : Nat.Prime 2468227535183 := by
  apply nodeValid_prime [2, 19, 64953356189] ⟨2468227535183, 5, [(2, 1), (19, 1), (64953356189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_64953356189
  · decide +kernel

theorem prime_4867601983201 : Nat.Prime 4867601983201 := by
  apply nodeValid_prime [2, 3, 5, 11, 61459621] ⟨4867601983201, 7, [(2, 5), (3, 2), (5, 2), (11, 1), (61459621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_61459621
  · decide +kernel

theorem prime_4867601983613 : Nat.Prime 4867601983613 := by
  apply nodeValid_prime [2, 3517, 9283, 37273] ⟨4867601983613, 2, [(2, 2), (3517, 1), (9283, 1), (37273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3517
    · exact prime_9283
    · exact prime_37273
  · decide +kernel

theorem prime_4867601998099 : Nat.Prime 4867601998099 := by
  apply nodeValid_prime [2, 3, 7, 29, 73, 83, 89, 7411] ⟨4867601998099, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (73, 1), (83, 1), (89, 1), (7411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_73
    · exact prime_83
    · exact prime_89
    · exact prime_7411
  · decide +kernel

theorem prime_4871409898933 : Nat.Prime 4871409898933 := by
  apply nodeValid_prime [2, 3, 112657, 1201141] ⟨4871409898933, 2, [(2, 2), (3, 2), (112657, 1), (1201141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_112657
    · exact prime_1201141
  · decide +kernel

theorem prime_4871409898991 : Nat.Prime 4871409898991 := by
  apply nodeValid_prime [2, 5, 17, 83, 229, 827, 1823] ⟨4871409898991, 11, [(2, 1), (5, 1), (17, 1), (83, 1), (229, 1), (827, 1), (1823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_83
    · exact prime_229
    · exact prime_827
    · exact prime_1823
  · decide +kernel

theorem prime_4871410018421 : Nat.Prime 4871410018421 := by
  apply nodeValid_prime [2, 5, 11, 22142772811] ⟨4871410018421, 2, [(2, 2), (5, 1), (11, 1), (22142772811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_22142772811
  · decide +kernel

theorem prime_4875220048129 : Nat.Prime 4875220048129 := by
  apply nodeValid_prime [2, 3, 4231, 1500341] ⟨4875220048129, 13, [(2, 8), (3, 1), (4231, 1), (1500341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4231
    · exact prime_1500341
  · decide +kernel

theorem prime_4875220048277 : Nat.Prime 4875220048277 := by
  apply nodeValid_prime [2, 1218805012069] ⟨4875220048277, 2, [(2, 2), (1218805012069, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1218805012069
  · decide +kernel

theorem prime_4875220051271 : Nat.Prime 4875220051271 := by
  apply nodeValid_prime [2, 5, 487522005127] ⟨4875220051271, 11, [(2, 1), (5, 1), (487522005127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_487522005127
  · decide +kernel

theorem prime_4879031975309 : Nat.Prime 4879031975309 := by
  apply nodeValid_prime [2, 47, 25952297741] ⟨4879031975309, 2, [(2, 2), (47, 1), (25952297741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_25952297741
  · decide +kernel

theorem prime_4879031976151 : Nat.Prime 4879031976151 := by
  apply nodeValid_prime [2, 3, 5, 17, 23, 8171, 10181] ⟨4879031976151, 6, [(2, 1), (3, 1), (5, 2), (17, 1), (23, 1), (8171, 1), (10181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_23
    · exact prime_8171
    · exact prime_10181
  · decide +kernel

theorem prime_4879032093631 : Nat.Prime 4879032093631 := by
  apply nodeValid_prime [2, 3, 5, 54211467707] ⟨4879032093631, 3, [(2, 1), (3, 2), (5, 1), (54211467707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_54211467707
  · decide +kernel

theorem prime_4882846018777 : Nat.Prime 4882846018777 := by
  apply nodeValid_prime [2, 3, 11, 31, 41, 14552029] ⟨4882846018777, 7, [(2, 3), (3, 1), (11, 1), (31, 1), (41, 1), (14552029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_31
    · exact prime_41
    · exact prime_14552029
  · decide +kernel

theorem prime_4882846019641 : Nat.Prime 4882846019641 := by
  apply nodeValid_prime [2, 3, 5, 167, 293, 831587] ⟨4882846019641, 23, [(2, 3), (3, 1), (5, 1), (167, 1), (293, 1), (831587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_167
    · exact prime_293
    · exact prime_831587
  · decide +kernel

theorem prime_4882846155653 : Nat.Prime 4882846155653 := by
  apply nodeValid_prime [2, 1220711538913] ⟨4882846155653, 2, [(2, 2), (1220711538913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1220711538913
  · decide +kernel

theorem prime_4886662223813 : Nat.Prime 4886662223813 := by
  apply nodeValid_prime [2, 1221665555953] ⟨4886662223813, 2, [(2, 2), (1221665555953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1221665555953
  · decide +kernel

theorem prime_4886662224329 : Nat.Prime 4886662224329 := by
  apply nodeValid_prime [2, 610832778041] ⟨4886662224329, 3, [(2, 3), (610832778041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_610832778041
  · decide +kernel

theorem prime_4886662237643 : Nat.Prime 4886662237643 := by
  apply nodeValid_prime [2, 2443331118821] ⟨4886662237643, 2, [(2, 1), (2443331118821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2443331118821
  · decide +kernel

theorem prime_4890480325649 : Nat.Prime 4890480325649 := by
  apply nodeValid_prime [2, 23, 463, 28702697] ⟨4890480325649, 3, [(2, 4), (23, 1), (463, 1), (28702697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_463
    · exact prime_28702697
  · decide +kernel

theorem prime_4890480327203 : Nat.Prime 4890480327203 := by
  apply nodeValid_prime [2, 479, 5104885519] ⟨4890480327203, 2, [(2, 1), (479, 1), (5104885519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_5104885519
  · decide +kernel

theorem prime_4890480335591 : Nat.Prime 4890480335591 := by
  apply nodeValid_prime [2, 5, 743, 1291, 509843] ⟨4890480335591, 7, [(2, 1), (5, 1), (743, 1), (1291, 1), (509843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_743
    · exact prime_1291
    · exact prime_509843
  · decide +kernel

theorem prime_4894300388167 : Nat.Prime 4894300388167 := by
  apply nodeValid_prime [2, 3, 7, 85991, 1355153] ⟨4894300388167, 3, [(2, 1), (3, 1), (7, 1), (85991, 1), (1355153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_85991
    · exact prime_1355153
  · decide +kernel

theorem prime_4894300388557 : Nat.Prime 4894300388557 := by
  apply nodeValid_prime [2, 3, 309011, 439961] ⟨4894300388557, 5, [(2, 2), (3, 2), (309011, 1), (439961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_309011
    · exact prime_439961
  · decide +kernel

theorem prime_4894300450499 : Nat.Prime 4894300450499 := by
  apply nodeValid_prime [2, 37, 217027, 304751] ⟨4894300450499, 2, [(2, 1), (37, 1), (217027, 1), (304751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_217027
    · exact prime_304751
  · decide +kernel

theorem prime_4898122585663 : Nat.Prime 4898122585663 := by
  apply nodeValid_prime [2, 3, 816353764277] ⟨4898122585663, 6, [(2, 1), (3, 1), (816353764277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_816353764277
  · decide +kernel

theorem prime_4898122595521 : Nat.Prime 4898122595521 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 17, 19, 271, 757] ⟨4898122595521, 59, [(2, 6), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (19, 1), (271, 1), (757, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_19
    · exact prime_271
    · exact prime_757
  · decide +kernel

theorem prime_4898122596089 : Nat.Prime 4898122596089 := by
  apply nodeValid_prime [2, 43, 491, 28999447] ⟨4898122596089, 3, [(2, 3), (43, 1), (491, 1), (28999447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_491
    · exact prime_28999447
  · decide +kernel

theorem prime_4901946742421 : Nat.Prime 4901946742421 := by
  apply nodeValid_prime [2, 5, 7, 13, 2693377331] ⟨4901946742421, 2, [(2, 2), (5, 1), (7, 1), (13, 1), (2693377331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_2693377331
  · decide +kernel

theorem prime_4901946841541 : Nat.Prime 4901946841541 := by
  apply nodeValid_prime [2, 5, 7, 601, 8322773] ⟨4901946841541, 3, [(2, 2), (5, 1), (7, 2), (601, 1), (8322773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_601
    · exact prime_8322773
  · decide +kernel

theorem prime_4901946842371 : Nat.Prime 4901946842371 := by
  apply nodeValid_prime [2, 3, 5, 19, 79, 8161, 13339] ⟨4901946842371, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (79, 1), (8161, 1), (13339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_79
    · exact prime_8161
    · exact prime_13339
  · decide +kernel

theorem prime_4905772917863 : Nat.Prime 4905772917863 := by
  apply nodeValid_prime [2, 2452886458931] ⟨4905772917863, 5, [(2, 1), (2452886458931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2452886458931
  · decide +kernel

theorem prime_4905772935509 : Nat.Prime 4905772935509 := by
  apply nodeValid_prime [2, 47, 257, 809, 125507] ⟨4905772935509, 2, [(2, 2), (47, 1), (257, 1), (809, 1), (125507, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_257
    · exact prime_809
    · exact prime_125507
  · decide +kernel

theorem prime_4905772935653 : Nat.Prime 4905772935653 := by
  apply nodeValid_prime [2, 29, 42291145997] ⟨4905772935653, 2, [(2, 2), (29, 1), (42291145997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_42291145997
  · decide +kernel

theorem prime_4909601086627 : Nat.Prime 4909601086627 := by
  apply nodeValid_prime [2, 3, 29, 28216098199] ⟨4909601086627, 2, [(2, 1), (3, 1), (29, 1), (28216098199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_28216098199
  · decide +kernel

theorem prime_4909601087089 : Nat.Prime 4909601087089 := by
  apply nodeValid_prime [2, 3, 102283355981] ⟨4909601087089, 7, [(2, 4), (3, 1), (102283355981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_102283355981
  · decide +kernel

theorem prime_4909601120293 : Nat.Prime 4909601120293 := by
  apply nodeValid_prime [2, 3, 11, 12397982627] ⟨4909601120293, 6, [(2, 2), (3, 2), (11, 1), (12397982627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_12397982627
  · decide +kernel

theorem prime_4913431342639 : Nat.Prime 4913431342639 := by
  apply nodeValid_prime [2, 3, 7, 13, 199, 227, 199211] ⟨4913431342639, 7, [(2, 1), (3, 1), (7, 1), (13, 1), (199, 1), (227, 1), (199211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_199
    · exact prime_227
    · exact prime_199211
  · decide +kernel

theorem prime_4913431520807 : Nat.Prime 4913431520807 := by
  apply nodeValid_prime [2, 67, 36667399409] ⟨4913431520807, 5, [(2, 1), (67, 1), (36667399409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_36667399409
  · decide +kernel

theorem prime_4913431520929 : Nat.Prime 4913431520929 := by
  apply nodeValid_prime [2, 3, 7, 17, 3614263] ⟨4913431520929, 29, [(2, 5), (3, 1), (7, 2), (17, 2), (3614263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_3614263
  · decide +kernel

theorem prime_4917263594813 : Nat.Prime 4917263594813 := by
  apply nodeValid_prime [2, 37, 829, 40078111] ⟨4917263594813, 2, [(2, 2), (37, 1), (829, 1), (40078111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_829
    · exact prime_40078111
  · decide +kernel

theorem prime_4917263681381 : Nat.Prime 4917263681381 := by
  apply nodeValid_prime [2, 5, 107, 131, 17540357] ⟨4917263681381, 2, [(2, 2), (5, 1), (107, 1), (131, 1), (17540357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_131
    · exact prime_17540357
  · decide +kernel

theorem prime_4917263683019 : Nat.Prime 4917263683019 := by
  apply nodeValid_prime [2, 283, 8687745023] ⟨4917263683019, 2, [(2, 1), (283, 1), (8687745023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_283
    · exact prime_8687745023
  · decide +kernel

theorem prime_4921097853337 : Nat.Prime 4921097853337 := by
  apply nodeValid_prime [2, 3, 7, 23, 373, 3414413] ⟨4921097853337, 5, [(2, 3), (3, 1), (7, 1), (23, 1), (373, 1), (3414413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_373
    · exact prime_3414413
  · decide +kernel

theorem prime_4921097923043 : Nat.Prime 4921097923043 := by
  apply nodeValid_prime [2, 7, 5059, 9925931] ⟨4921097923043, 6, [(2, 1), (7, 2), (5059, 1), (9925931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_5059
    · exact prime_9925931
  · decide +kernel

theorem prime_4921097923727 : Nat.Prime 4921097923727 := by
  apply nodeValid_prime [2, 2609, 943100407] ⟨4921097923727, 5, [(2, 1), (2609, 1), (943100407, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2609
    · exact prime_943100407
  · decide +kernel

theorem prime_4924934132959 : Nat.Prime 4924934132959 := by
  apply nodeValid_prime [2, 3, 7, 39086778833] ⟨4924934132959, 3, [(2, 1), (3, 2), (7, 1), (39086778833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_39086778833
  · decide +kernel

theorem prime_4924934198039 : Nat.Prime 4924934198039 := by
  apply nodeValid_prime [2, 31, 15937, 4984277] ⟨4924934198039, 7, [(2, 1), (31, 1), (15937, 1), (4984277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_15937
    · exact prime_4984277
  · decide +kernel

theorem prime_4924934198603 : Nat.Prime 4924934198603 := by
  apply nodeValid_prime [2, 11, 223860645391] ⟨4924934198603, 2, [(2, 1), (11, 1), (223860645391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_223860645391
  · decide +kernel

theorem prime_4928772426769 : Nat.Prime 4928772426769 := by
  apply nodeValid_prime [2, 3, 31, 43, 25677109] ⟨4928772426769, 29, [(2, 4), (3, 2), (31, 1), (43, 1), (25677109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_43
    · exact prime_25677109
  · decide +kernel

theorem prime_4928772456701 : Nat.Prime 4928772456701 := by
  apply nodeValid_prime [2, 5, 49287724567] ⟨4928772456701, 2, [(2, 2), (5, 2), (49287724567, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49287724567
  · decide +kernel

theorem prime_4928772457993 : Nat.Prime 4928772457993 := by
  apply nodeValid_prime [2, 3, 491, 418259713] ⟨4928772457993, 7, [(2, 3), (3, 1), (491, 1), (418259713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_491
    · exact prime_418259713
  · decide +kernel

theorem prime_4932612544459 : Nat.Prime 4932612544459 := by
  apply nodeValid_prime [2, 3, 127, 2521, 2567729] ⟨4932612544459, 10, [(2, 1), (3, 1), (127, 1), (2521, 1), (2567729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_2521
    · exact prime_2567729
  · decide +kernel

theorem prime_4932612545177 : Nat.Prime 4932612545177 := by
  apply nodeValid_prime [2, 17, 36269209891] ⟨4932612545177, 3, [(2, 3), (17, 1), (36269209891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_36269209891
  · decide +kernel

theorem prime_4932612741619 : Nat.Prime 4932612741619 := by
  apply nodeValid_prime [2, 3, 274034041201] ⟨4932612741619, 2, [(2, 1), (3, 2), (274034041201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_274034041201
  · decide +kernel

theorem prime_4936455070367 : Nat.Prime 4936455070367 := by
  apply nodeValid_prime [2, 2468227535183] ⟨4936455070367, 5, [(2, 1), (2468227535183, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2468227535183
  · decide +kernel

theorem prime_4936455129257 : Nat.Prime 4936455129257 := by
  apply nodeValid_prime [2, 7, 29, 41, 281, 439, 601] ⟨4936455129257, 3, [(2, 3), (7, 1), (29, 1), (41, 1), (281, 1), (439, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_41
    · exact prime_281
    · exact prime_439
    · exact prime_601
  · decide +kernel

theorem prime_4936455133457 : Nat.Prime 4936455133457 := by
  apply nodeValid_prime [2, 7, 11, 31, 129253643] ⟨4936455133457, 3, [(2, 4), (7, 1), (11, 1), (31, 1), (129253643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_129253643
  · decide +kernel

theorem prime_4940299272641 : Nat.Prime 4940299272641 := by
  apply nodeValid_prime [2, 5, 367, 42066581] ⟨4940299272641, 3, [(2, 6), (5, 1), (367, 1), (42066581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_367
    · exact prime_42066581
  · decide +kernel

theorem prime_4940299273163 : Nat.Prime 4940299273163 := by
  apply nodeValid_prime [2, 11, 224559057871] ⟨4940299273163, 2, [(2, 1), (11, 1), (224559057871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_224559057871
  · decide +kernel

theorem prime_4940299418543 : Nat.Prime 4940299418543 := by
  apply nodeValid_prime [2, 47, 1697, 30970169] ⟨4940299418543, 5, [(2, 1), (47, 1), (1697, 1), (30970169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_1697
    · exact prime_30970169
  · decide +kernel

theorem prime_4944145800067 : Nat.Prime 4944145800067 := by
  apply nodeValid_prime [2, 3, 11, 213287, 351223] ⟨4944145800067, 2, [(2, 1), (3, 1), (11, 1), (213287, 1), (351223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_213287
    · exact prime_351223
  · decide +kernel

theorem prime_4944145869227 : Nat.Prime 4944145869227 := by
  apply nodeValid_prime [2, 29, 85243894297] ⟨4944145869227, 2, [(2, 1), (29, 1), (85243894297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_85243894297
  · decide +kernel

theorem prime_4944145869941 : Nat.Prime 4944145869941 := by
  apply nodeValid_prime [2, 5, 247207293497] ⟨4944145869941, 2, [(2, 2), (5, 1), (247207293497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_247207293497
  · decide +kernel

theorem prime_4947994175923 : Nat.Prime 4947994175923 := by
  apply nodeValid_prime [2, 3, 7, 647, 8670743] ⟨4947994175923, 2, [(2, 1), (3, 2), (7, 2), (647, 1), (8670743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_647
    · exact prime_8670743
  · decide +kernel

theorem prime_4947994176101 : Nat.Prime 4947994176101 := by
  apply nodeValid_prime [2, 5, 337, 827, 177539] ⟨4947994176101, 2, [(2, 2), (5, 2), (337, 1), (827, 1), (177539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_337
    · exact prime_827
    · exact prime_177539
  · decide +kernel

theorem prime_4947994206271 : Nat.Prime 4947994206271 := by
  apply nodeValid_prime [2, 3, 5, 8447, 6508549] ⟨4947994206271, 7, [(2, 1), (3, 2), (5, 1), (8447, 1), (6508549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_8447
    · exact prime_6508549
  · decide +kernel

theorem prime_4951844647703 : Nat.Prime 4951844647703 := by
  apply nodeValid_prime [2, 929, 2665147819] ⟨4951844647703, 5, [(2, 1), (929, 1), (2665147819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_929
    · exact prime_2665147819
  · decide +kernel

theorem prime_4951844696347 : Nat.Prime 4951844696347 := by
  apply nodeValid_prime [2, 3, 17, 2855735119] ⟨4951844696347, 2, [(2, 1), (3, 1), (17, 2), (2855735119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2855735119
  · decide +kernel

theorem prime_4951844697829 : Nat.Prime 4951844697829 := by
  apply nodeValid_prime [2, 3, 7, 58950532117] ⟨4951844697829, 2, [(2, 2), (3, 1), (7, 1), (58950532117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_58950532117
  · decide +kernel

theorem prime_4955697114619 : Nat.Prime 4955697114619 := by
  apply nodeValid_prime [2, 3, 825949519103] ⟨4955697114619, 2, [(2, 1), (3, 1), (825949519103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_825949519103
  · decide +kernel

theorem prime_4955697127721 : Nat.Prime 4955697127721 := by
  apply nodeValid_prime [2, 5, 61, 5297, 383429] ⟨4955697127721, 3, [(2, 3), (5, 1), (61, 1), (5297, 1), (383429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_5297
    · exact prime_383429
  · decide +kernel

theorem prime_4955697128867 : Nat.Prime 4955697128867 := by
  apply nodeValid_prime [2, 11, 107, 109, 241, 80141] ⟨4955697128867, 2, [(2, 1), (11, 1), (107, 1), (109, 1), (241, 1), (80141, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_107
    · exact prime_109
    · exact prime_241
    · exact prime_80141
  · decide +kernel

theorem prime_4959551614603 : Nat.Prime 4959551614603 := by
  apply nodeValid_prime [2, 3, 13, 4891076543] ⟨4959551614603, 2, [(2, 1), (3, 1), (13, 2), (4891076543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4891076543
  · decide +kernel

theorem prime_4959551636099 : Nat.Prime 4959551636099 := by
  apply nodeValid_prime [2, 59, 89, 5167, 91397] ⟨4959551636099, 2, [(2, 1), (59, 1), (89, 1), (5167, 1), (91397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_89
    · exact prime_5167
    · exact prime_91397
  · decide +kernel

theorem prime_4959551636821 : Nat.Prime 4959551636821 := by
  apply nodeValid_prime [2, 3, 5, 11, 193, 4326121] ⟨4959551636821, 2, [(2, 2), (3, 3), (5, 1), (11, 1), (193, 1), (4326121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_193
    · exact prime_4326121
  · decide +kernel

end Sude.Lucas.Generated
