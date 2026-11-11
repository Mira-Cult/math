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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0047
import Sude.GeneratedFTT.N0048
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0063
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0083
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0097
import Sude.GeneratedFTT.N0102
import Sude.GeneratedFTT.N0104

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_9323 : Nat.Prime 9323 := by
  apply nodeValid_prime [2, 59, 79] ⟨9323, 2, [(2, 1), (59, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_79
  · decide +kernel

theorem prime_11149 : Nat.Prime 11149 := by
  apply nodeValid_prime [2, 3, 929] ⟨11149, 10, [(2, 2), (3, 1), (929, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_929
  · decide +kernel

theorem prime_12841 : Nat.Prime 12841 := by
  apply nodeValid_prime [2, 3, 5, 107] ⟨12841, 21, [(2, 3), (3, 1), (5, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_107
  · decide +kernel

theorem prime_16073 : Nat.Prime 16073 := by
  apply nodeValid_prime [2, 7, 41] ⟨16073, 3, [(2, 3), (7, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
  · decide +kernel

theorem prime_18553 : Nat.Prime 18553 := by
  apply nodeValid_prime [2, 3, 773] ⟨18553, 5, [(2, 3), (3, 1), (773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_773
  · decide +kernel

theorem prime_19927 : Nat.Prime 19927 := by
  apply nodeValid_prime [2, 3, 41] ⟨19927, 6, [(2, 1), (3, 5), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_21283 : Nat.Prime 21283 := by
  apply nodeValid_prime [2, 3, 3547] ⟨21283, 11, [(2, 1), (3, 1), (3547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3547
  · decide +kernel

theorem prime_23447 : Nat.Prime 23447 := by
  apply nodeValid_prime [2, 19, 617] ⟨23447, 5, [(2, 1), (19, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_617
  · decide +kernel

theorem prime_23789 : Nat.Prime 23789 := by
  apply nodeValid_prime [2, 19, 313] ⟨23789, 2, [(2, 2), (19, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_313
  · decide +kernel

theorem prime_33941 : Nat.Prime 33941 := by
  apply nodeValid_prime [2, 5, 1697] ⟨33941, 2, [(2, 2), (5, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1697
  · decide +kernel

theorem prime_37097 : Nat.Prime 37097 := by
  apply nodeValid_prime [2, 4637] ⟨37097, 3, [(2, 3), (4637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4637
  · decide +kernel

theorem prime_37199 : Nat.Prime 37199 := by
  apply nodeValid_prime [2, 7, 2657] ⟨37199, 7, [(2, 1), (7, 1), (2657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2657
  · decide +kernel

theorem prime_37897 : Nat.Prime 37897 := by
  apply nodeValid_prime [2, 3, 1579] ⟨37897, 5, [(2, 3), (3, 1), (1579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1579
  · decide +kernel

theorem prime_38677 : Nat.Prime 38677 := by
  apply nodeValid_prime [2, 3, 11, 293] ⟨38677, 5, [(2, 2), (3, 1), (11, 1), (293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_293
  · decide +kernel

theorem prime_50767 : Nat.Prime 50767 := by
  apply nodeValid_prime [2, 3, 8461] ⟨50767, 5, [(2, 1), (3, 1), (8461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8461
  · decide +kernel

theorem prime_53699 : Nat.Prime 53699 := by
  apply nodeValid_prime [2, 26849] ⟨53699, 2, [(2, 1), (26849, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26849
  · decide +kernel

theorem prime_54167 : Nat.Prime 54167 := by
  apply nodeValid_prime [2, 7, 53, 73] ⟨54167, 5, [(2, 1), (7, 1), (53, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
    · exact prime_73
  · decide +kernel

theorem prime_56437 : Nat.Prime 56437 := by
  apply nodeValid_prime [2, 3, 4703] ⟨56437, 2, [(2, 2), (3, 1), (4703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4703
  · decide +kernel

theorem prime_61961 : Nat.Prime 61961 := by
  apply nodeValid_prime [2, 5, 1549] ⟨61961, 3, [(2, 3), (5, 1), (1549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1549
  · decide +kernel

theorem prime_62383 : Nat.Prime 62383 := by
  apply nodeValid_prime [2, 3, 37, 281] ⟨62383, 5, [(2, 1), (3, 1), (37, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_281
  · decide +kernel

theorem prime_64373 : Nat.Prime 64373 := by
  apply nodeValid_prime [2, 7, 11, 19] ⟨64373, 2, [(2, 2), (7, 1), (11, 2), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
  · decide +kernel

theorem prime_71963 : Nat.Prime 71963 := by
  apply nodeValid_prime [2, 11, 3271] ⟨71963, 2, [(2, 1), (11, 1), (3271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3271
  · decide +kernel

theorem prime_77641 : Nat.Prime 77641 := by
  apply nodeValid_prime [2, 3, 5, 647] ⟨77641, 13, [(2, 3), (3, 1), (5, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_647
  · decide +kernel

theorem prime_87253 : Nat.Prime 87253 := by
  apply nodeValid_prime [2, 3, 11, 661] ⟨87253, 2, [(2, 2), (3, 1), (11, 1), (661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_661
  · decide +kernel

theorem prime_106411 : Nat.Prime 106411 := by
  apply nodeValid_prime [2, 3, 5, 3547] ⟨106411, 2, [(2, 1), (3, 1), (5, 1), (3547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3547
  · decide +kernel

theorem prime_122449 : Nat.Prime 122449 := by
  apply nodeValid_prime [2, 3, 2551] ⟨122449, 7, [(2, 4), (3, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2551
  · decide +kernel

theorem prime_128747 : Nat.Prime 128747 := by
  apply nodeValid_prime [2, 64373] ⟨128747, 2, [(2, 1), (64373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_64373
  · decide +kernel

theorem prime_138581 : Nat.Prime 138581 := by
  apply nodeValid_prime [2, 5, 13, 41] ⟨138581, 3, [(2, 2), (5, 1), (13, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_41
  · decide +kernel

theorem prime_139459 : Nat.Prime 139459 := by
  apply nodeValid_prime [2, 3, 11, 2113] ⟨139459, 2, [(2, 1), (3, 1), (11, 1), (2113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_2113
  · decide +kernel

theorem prime_140839 : Nat.Prime 140839 := by
  apply nodeValid_prime [2, 3, 23473] ⟨140839, 6, [(2, 1), (3, 1), (23473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23473
  · decide +kernel

theorem prime_169777 : Nat.Prime 169777 := by
  apply nodeValid_prime [2, 3, 131] ⟨169777, 5, [(2, 4), (3, 4), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_131
  · decide +kernel

theorem prime_172643 : Nat.Prime 172643 := by
  apply nodeValid_prime [2, 37, 2333] ⟨172643, 2, [(2, 1), (37, 1), (2333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2333
  · decide +kernel

theorem prime_178559 : Nat.Prime 178559 := by
  apply nodeValid_prime [2, 73, 1223] ⟨178559, 19, [(2, 1), (73, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_1223
  · decide +kernel

theorem prime_185531 : Nat.Prime 185531 := by
  apply nodeValid_prime [2, 5, 18553] ⟨185531, 2, [(2, 1), (5, 1), (18553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_18553
  · decide +kernel

theorem prime_190313 : Nat.Prime 190313 := by
  apply nodeValid_prime [2, 23789] ⟨190313, 3, [(2, 3), (23789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23789
  · decide +kernel

theorem prime_212057 : Nat.Prime 212057 := by
  apply nodeValid_prime [2, 13, 2039] ⟨212057, 3, [(2, 3), (13, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2039
  · decide +kernel

theorem prime_212467 : Nat.Prime 212467 := by
  apply nodeValid_prime [2, 3, 17, 2083] ⟨212467, 2, [(2, 1), (3, 1), (17, 1), (2083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_2083
  · decide +kernel

theorem prime_246131 : Nat.Prime 246131 := by
  apply nodeValid_prime [2, 5, 151, 163] ⟨246131, 2, [(2, 1), (5, 1), (151, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_163
  · decide +kernel

theorem prime_255077 : Nat.Prime 255077 := by
  apply nodeValid_prime [2, 43, 1483] ⟨255077, 2, [(2, 2), (43, 1), (1483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_1483
  · decide +kernel

theorem prime_280547 : Nat.Prime 280547 := by
  apply nodeValid_prime [2, 7, 29, 691] ⟨280547, 5, [(2, 1), (7, 1), (29, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_691
  · decide +kernel

theorem prime_341587 : Nat.Prime 341587 := by
  apply nodeValid_prime [2, 3, 7, 2711] ⟨341587, 2, [(2, 1), (3, 2), (7, 1), (2711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2711
  · decide +kernel

theorem prime_370387 : Nat.Prime 370387 := by
  apply nodeValid_prime [2, 3, 19] ⟨370387, 5, [(2, 1), (3, 3), (19, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_445589 : Nat.Prime 445589 := by
  apply nodeValid_prime [2, 11, 13, 19, 41] ⟨445589, 2, [(2, 2), (11, 1), (13, 1), (19, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_19
    · exact prime_41
  · decide +kernel

theorem prime_455053 : Nat.Prime 455053 := by
  apply nodeValid_prime [2, 3, 13, 2917] ⟨455053, 2, [(2, 2), (3, 1), (13, 1), (2917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2917
  · decide +kernel

theorem prime_563357 : Nat.Prime 563357 := by
  apply nodeValid_prime [2, 140839] ⟨563357, 2, [(2, 2), (140839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_140839
  · decide +kernel

theorem prime_646643 : Nat.Prime 646643 := by
  apply nodeValid_prime [2, 29, 11149] ⟨646643, 2, [(2, 1), (29, 1), (11149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_11149
  · decide +kernel

theorem prime_746233 : Nat.Prime 746233 := by
  apply nodeValid_prime [2, 3, 17, 31, 59] ⟨746233, 5, [(2, 3), (3, 1), (17, 1), (31, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_31
    · exact prime_59
  · decide +kernel

theorem prime_775573 : Nat.Prime 775573 := by
  apply nodeValid_prime [2, 3, 7, 1319] ⟨775573, 5, [(2, 2), (3, 1), (7, 2), (1319, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1319
  · decide +kernel

theorem prime_849869 : Nat.Prime 849869 := by
  apply nodeValid_prime [2, 212467] ⟨849869, 2, [(2, 2), (212467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_212467
  · decide +kernel

theorem prime_888809 : Nat.Prime 888809 := by
  apply nodeValid_prime [2, 241, 461] ⟨888809, 3, [(2, 3), (241, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_241
    · exact prime_461
  · decide +kernel

theorem prime_899321 : Nat.Prime 899321 := by
  apply nodeValid_prime [2, 5, 22483] ⟨899321, 3, [(2, 3), (5, 1), (22483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_22483
  · decide +kernel

theorem prime_901213 : Nat.Prime 901213 := by
  apply nodeValid_prime [2, 3, 13, 53, 109] ⟨901213, 2, [(2, 2), (3, 1), (13, 1), (53, 1), (109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_109
  · decide +kernel

theorem prime_926533 : Nat.Prime 926533 := by
  apply nodeValid_prime [2, 3, 23, 373] ⟨926533, 2, [(2, 2), (3, 3), (23, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_373
  · decide +kernel

theorem prime_941747 : Nat.Prime 941747 := by
  apply nodeValid_prime [2, 13, 29, 1249] ⟨941747, 5, [(2, 1), (13, 1), (29, 1), (1249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_1249
  · decide +kernel

theorem prime_1366349 : Nat.Prime 1366349 := by
  apply nodeValid_prime [2, 341587] ⟨1366349, 2, [(2, 2), (341587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_341587
  · decide +kernel

theorem prime_1387669 : Nat.Prime 1387669 := by
  apply nodeValid_prime [2, 3, 197, 587] ⟨1387669, 2, [(2, 2), (3, 1), (197, 1), (587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_587
  · decide +kernel

theorem prime_1394891 : Nat.Prime 1394891 := by
  apply nodeValid_prime [2, 5, 7, 19927] ⟨1394891, 2, [(2, 1), (5, 1), (7, 1), (19927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_19927
  · decide +kernel

theorem prime_1558643 : Nat.Prime 1558643 := by
  apply nodeValid_prime [2, 619, 1259] ⟨1558643, 2, [(2, 1), (619, 1), (1259, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_619
    · exact prime_1259
  · decide +kernel

theorem prime_1663619 : Nat.Prime 1663619 := by
  apply nodeValid_prime [2, 11, 75619] ⟨1663619, 2, [(2, 1), (11, 1), (75619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_75619
  · decide +kernel

theorem prime_1820213 : Nat.Prime 1820213 := by
  apply nodeValid_prime [2, 455053] ⟨1820213, 2, [(2, 2), (455053, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_455053
  · decide +kernel

theorem prime_1827613 : Nat.Prime 1827613 := by
  apply nodeValid_prime [2, 3, 50767] ⟨1827613, 2, [(2, 2), (3, 2), (50767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50767
  · decide +kernel

theorem prime_2353781 : Nat.Prime 2353781 := by
  apply nodeValid_prime [2, 5, 11, 13, 823] ⟨2353781, 3, [(2, 2), (5, 1), (11, 1), (13, 1), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_823
  · decide +kernel

theorem prime_2545481 : Nat.Prime 2545481 := by
  apply nodeValid_prime [2, 5, 7, 9091] ⟨2545481, 3, [(2, 3), (5, 1), (7, 1), (9091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_9091
  · decide +kernel

theorem prime_3577897 : Nat.Prime 3577897 := by
  apply nodeValid_prime [2, 3, 7, 31, 229] ⟨3577897, 30, [(2, 3), (3, 2), (7, 1), (31, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_229
  · decide +kernel

theorem prime_3706133 : Nat.Prime 3706133 := by
  apply nodeValid_prime [2, 926533] ⟨3706133, 2, [(2, 2), (926533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_926533
  · decide +kernel

theorem prime_3769411 : Nat.Prime 3769411 := by
  apply nodeValid_prime [2, 3, 5, 17, 19, 389] ⟨3769411, 2, [(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_19
    · exact prime_389
  · decide +kernel

theorem prime_4454383 : Nat.Prime 4454383 := by
  apply nodeValid_prime [2, 3, 59, 12583] ⟨4454383, 5, [(2, 1), (3, 1), (59, 1), (12583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_12583
  · decide +kernel

theorem prime_4591387 : Nat.Prime 4591387 := by
  apply nodeValid_prime [2, 3, 255077] ⟨4591387, 2, [(2, 1), (3, 2), (255077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_255077
  · decide +kernel

theorem prime_4599337 : Nat.Prime 4599337 := by
  apply nodeValid_prime [2, 3, 7, 3911] ⟨4599337, 5, [(2, 3), (3, 1), (7, 2), (3911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_3911
  · decide +kernel

theorem prime_6055453 : Nat.Prime 6055453 := by
  apply nodeValid_prime [2, 3, 13, 19, 227] ⟨6055453, 2, [(2, 2), (3, 3), (13, 1), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_8513201 : Nat.Prime 8513201 := by
  apply nodeValid_prime [2, 5, 21283] ⟨8513201, 3, [(2, 4), (5, 2), (21283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_21283
  · decide +kernel

theorem prime_8848429 : Nat.Prime 8848429 := by
  apply nodeValid_prime [2, 3, 599, 1231] ⟨8848429, 11, [(2, 2), (3, 1), (599, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_599
    · exact prime_1231
  · decide +kernel

theorem prime_9314267 : Nat.Prime 9314267 := by
  apply nodeValid_prime [2, 13, 17, 1621] ⟨9314267, 5, [(2, 1), (13, 2), (17, 1), (1621, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_1621
  · decide +kernel

theorem prime_11137571 : Nat.Prime 11137571 := by
  apply nodeValid_prime [2, 5, 743, 1499] ⟨11137571, 6, [(2, 1), (5, 1), (743, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_743
    · exact prime_1499
  · decide +kernel

theorem prime_13212007 : Nat.Prime 13212007 := by
  apply nodeValid_prime [2, 3, 137, 16073] ⟨13212007, 3, [(2, 1), (3, 1), (137, 1), (16073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_16073
  · decide +kernel

theorem prime_13519903 : Nat.Prime 13519903 := by
  apply nodeValid_prime [2, 3, 11, 79, 2593] ⟨13519903, 3, [(2, 1), (3, 1), (11, 1), (79, 1), (2593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_79
    · exact prime_2593
  · decide +kernel

theorem prime_15494209 : Nat.Prime 15494209 := by
  apply nodeValid_prime [2, 3, 17, 47, 101] ⟨15494209, 7, [(2, 6), (3, 1), (17, 1), (47, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_47
    · exact prime_101
  · decide +kernel

theorem prime_15709693 : Nat.Prime 15709693 := by
  apply nodeValid_prime [2, 3, 827, 1583] ⟨15709693, 2, [(2, 2), (3, 1), (827, 1), (1583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_827
    · exact prime_1583
  · decide +kernel

theorem prime_18613753 : Nat.Prime 18613753 := by
  apply nodeValid_prime [2, 3, 775573] ⟨18613753, 5, [(2, 3), (3, 1), (775573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_775573
  · decide +kernel

theorem prime_18703717 : Nat.Prime 18703717 := by
  apply nodeValid_prime [2, 3, 1558643] ⟨18703717, 2, [(2, 2), (3, 1), (1558643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1558643
  · decide +kernel

theorem prime_20447131 : Nat.Prime 20447131 := by
  apply nodeValid_prime [2, 3, 5, 11, 61961] ⟨20447131, 15, [(2, 1), (3, 1), (5, 1), (11, 1), (61961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_61961
  · decide +kernel

theorem prime_21370511 : Nat.Prime 21370511 := by
  apply nodeValid_prime [2, 5, 7, 397, 769] ⟨21370511, 7, [(2, 1), (5, 1), (7, 1), (397, 1), (769, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_397
    · exact prime_769
  · decide +kernel

theorem prime_23929289 : Nat.Prime 23929289 := by
  apply nodeValid_prime [2, 53, 56437] ⟨23929289, 6, [(2, 3), (53, 1), (56437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_56437
  · decide +kernel

theorem prime_24552373 : Nat.Prime 24552373 := by
  apply nodeValid_prime [2, 3, 13, 31, 5077] ⟨24552373, 6, [(2, 2), (3, 1), (13, 1), (31, 1), (5077, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
    · exact prime_5077
  · decide +kernel

theorem prime_27080717 : Nat.Prime 27080717 := by
  apply nodeValid_prime [2, 13, 199, 2617] ⟨27080717, 2, [(2, 2), (13, 1), (199, 1), (2617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_199
    · exact prime_2617
  · decide +kernel

theorem prime_41609059 : Nat.Prime 41609059 := by
  apply nodeValid_prime [2, 3, 1399, 4957] ⟨41609059, 3, [(2, 1), (3, 1), (1399, 1), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1399
    · exact prime_4957
  · decide +kernel

theorem prime_47036783 : Nat.Prime 47036783 := by
  apply nodeValid_prime [2, 13, 29, 62383] ⟨47036783, 5, [(2, 1), (13, 1), (29, 1), (62383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_29
    · exact prime_62383
  · decide +kernel

theorem prime_48005537 : Nat.Prime 48005537 := by
  apply nodeValid_prime [2, 61, 24593] ⟨48005537, 3, [(2, 5), (61, 1), (24593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_24593
  · decide +kernel

theorem prime_58924471 : Nat.Prime 58924471 := by
  apply nodeValid_prime [2, 3, 5, 11, 178559] ⟨58924471, 23, [(2, 1), (3, 1), (5, 1), (11, 1), (178559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_178559
  · decide +kernel

theorem prime_69271711 : Nat.Prime 69271711 := by
  apply nodeValid_prime [2, 3, 5, 43, 53699] ⟨69271711, 3, [(2, 1), (3, 1), (5, 1), (43, 1), (53699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_53699
  · decide +kernel

theorem prime_70145903 : Nat.Prime 70145903 := by
  apply nodeValid_prime [2, 47, 746233] ⟨70145903, 5, [(2, 1), (47, 1), (746233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_746233
  · decide +kernel

theorem prime_117347267 : Nat.Prime 117347267 := by
  apply nodeValid_prime [2, 4219, 13907] ⟨117347267, 2, [(2, 1), (4219, 1), (13907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4219
    · exact prime_13907
  · decide +kernel

theorem prime_122066513 : Nat.Prime 122066513 := by
  apply nodeValid_prime [2, 41, 73, 2549] ⟨122066513, 3, [(2, 4), (41, 1), (73, 1), (2549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_73
    · exact prime_2549
  · decide +kernel

theorem prime_194720179 : Nat.Prime 194720179 := by
  apply nodeValid_prime [2, 3, 59, 9323] ⟨194720179, 2, [(2, 1), (3, 1), (59, 2), (9323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_9323
  · decide +kernel

theorem prime_244133027 : Nat.Prime 244133027 := by
  apply nodeValid_prime [2, 122066513] ⟨244133027, 2, [(2, 1), (122066513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_122066513
  · decide +kernel

theorem prime_246645649 : Nat.Prime 246645649 := by
  apply nodeValid_prime [2, 3, 190313] ⟨246645649, 7, [(2, 4), (3, 4), (190313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_190313
  · decide +kernel

theorem prime_262276813 : Nat.Prime 262276813 := by
  apply nodeValid_prime [2, 3, 7, 29, 1709] ⟨262276813, 11, [(2, 2), (3, 3), (7, 2), (29, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29
    · exact prime_1709
  · decide +kernel

theorem prime_266127479 : Nat.Prime 266127479 := by
  apply nodeValid_prime [2, 5227, 25457] ⟨266127479, 7, [(2, 1), (5227, 1), (25457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5227
    · exact prime_25457
  · decide +kernel

theorem prime_305235137 : Nat.Prime 305235137 := by
  apply nodeValid_prime [2, 17, 280547] ⟨305235137, 3, [(2, 6), (17, 1), (280547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_280547
  · decide +kernel

theorem prime_359794861 : Nat.Prime 359794861 := by
  apply nodeValid_prime [2, 3, 5, 257, 23333] ⟨359794861, 2, [(2, 2), (3, 1), (5, 1), (257, 1), (23333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_257
    · exact prime_23333
  · decide +kernel

theorem prime_430727203 : Nat.Prime 430727203 := by
  apply nodeValid_prime [2, 3, 23929289] ⟨430727203, 2, [(2, 1), (3, 2), (23929289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23929289
  · decide +kernel

theorem prime_489029369 : Nat.Prime 489029369 := by
  apply nodeValid_prime [2, 43, 89, 15973] ⟨489029369, 6, [(2, 3), (43, 1), (89, 1), (15973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_89
    · exact prime_15973
  · decide +kernel

theorem prime_605796089 : Nat.Prime 605796089 := by
  apply nodeValid_prime [2, 17, 4454383] ⟨605796089, 3, [(2, 3), (17, 1), (4454383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_4454383
  · decide +kernel

theorem prime_673923881 : Nat.Prime 673923881 := by
  apply nodeValid_prime [2, 5, 7, 31, 77641] ⟨673923881, 3, [(2, 3), (5, 1), (7, 1), (31, 1), (77641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_31
    · exact prime_77641
  · decide +kernel

theorem prime_685805231 : Nat.Prime 685805231 := by
  apply nodeValid_prime [2, 5, 11, 877, 7109] ⟨685805231, 13, [(2, 1), (5, 1), (11, 1), (877, 1), (7109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_877
    · exact prime_7109
  · decide +kernel

theorem prime_865273793 : Nat.Prime 865273793 := by
  apply nodeValid_prime [2, 13519903] ⟨865273793, 3, [(2, 6), (13519903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13519903
  · decide +kernel

theorem prime_1464798163 : Nat.Prime 1464798163 := by
  apply nodeValid_prime [2, 3, 244133027] ⟨1464798163, 3, [(2, 1), (3, 1), (244133027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_244133027
  · decide +kernel

theorem prime_1576766747 : Nat.Prime 1576766747 := by
  apply nodeValid_prime [2, 577, 1366349] ⟨1576766747, 2, [(2, 1), (577, 1), (1366349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_1366349
  · decide +kernel

theorem prime_2061912157 : Nat.Prime 2061912157 := by
  apply nodeValid_prime [2, 3, 73, 2353781] ⟨2061912157, 2, [(2, 2), (3, 1), (73, 1), (2353781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_2353781
  · decide +kernel

theorem prime_2220666473 : Nat.Prime 2220666473 := by
  apply nodeValid_prime [2, 199, 1394891] ⟨2220666473, 3, [(2, 3), (199, 1), (1394891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_1394891
  · decide +kernel

theorem prime_2979908143 : Nat.Prime 2979908143 := by
  apply nodeValid_prime [2, 3, 12841, 38677] ⟨2979908143, 3, [(2, 1), (3, 1), (12841, 1), (38677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_12841
    · exact prime_38677
  · decide +kernel

theorem prime_3365533793 : Nat.Prime 3365533793 := by
  apply nodeValid_prime [2, 17, 2267, 2729] ⟨3365533793, 3, [(2, 5), (17, 1), (2267, 1), (2729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_2267
    · exact prime_2729
  · decide +kernel

theorem prime_4283843939 : Nat.Prime 4283843939 := by
  apply nodeValid_prime [2, 11, 194720179] ⟨4283843939, 2, [(2, 1), (11, 1), (194720179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_194720179
  · decide +kernel

theorem prime_4343452103 : Nat.Prime 4343452103 := by
  apply nodeValid_prime [2, 11, 43, 4591387] ⟨4343452103, 5, [(2, 1), (11, 1), (43, 1), (4591387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_43
    · exact prime_4591387
  · decide +kernel

theorem prime_5163279749 : Nat.Prime 5163279749 := by
  apply nodeValid_prime [2, 11, 117347267] ⟨5163279749, 2, [(2, 2), (11, 1), (117347267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_117347267
  · decide +kernel

theorem prime_7878222701 : Nat.Prime 7878222701 := by
  apply nodeValid_prime [2, 5, 19, 853, 4861] ⟨7878222701, 2, [(2, 2), (5, 2), (19, 1), (853, 1), (4861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_853
    · exact prime_4861
  · decide +kernel

theorem prime_9430799341 : Nat.Prime 9430799341 := by
  apply nodeValid_prime [2, 3, 5, 19, 223, 37097] ⟨9430799341, 2, [(2, 2), (3, 1), (5, 1), (19, 1), (223, 1), (37097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_223
    · exact prime_37097
  · decide +kernel

theorem prime_11589996683 : Nat.Prime 11589996683 := by
  apply nodeValid_prime [2, 11, 29, 107, 169777] ⟨11589996683, 2, [(2, 1), (11, 1), (29, 1), (107, 1), (169777, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_107
    · exact prime_169777
  · decide +kernel

theorem prime_14724364799 : Nat.Prime 14724364799 := by
  apply nodeValid_prime [2, 11, 13, 139, 370387] ⟨14724364799, 7, [(2, 1), (11, 1), (13, 1), (139, 1), (370387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_13
    · exact prime_139
    · exact prime_370387
  · decide +kernel

theorem prime_20724883979 : Nat.Prime 20724883979 := by
  apply nodeValid_prime [2, 43, 6359, 37897] ⟨20724883979, 2, [(2, 1), (43, 1), (6359, 1), (37897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_6359
    · exact prime_37897
  · decide +kernel

theorem prime_22413845833 : Nat.Prime 22413845833 := by
  apply nodeValid_prime [2, 3, 7, 73, 1827613] ⟨22413845833, 5, [(2, 3), (3, 1), (7, 1), (73, 1), (1827613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
    · exact prime_1827613
  · decide +kernel

theorem prime_32862823967 : Nat.Prime 32862823967 := by
  apply nodeValid_prime [2, 7, 19, 139, 888809] ⟨32862823967, 5, [(2, 1), (7, 1), (19, 1), (139, 1), (888809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_139
    · exact prime_888809
  · decide +kernel

theorem prime_37263066593 : Nat.Prime 37263066593 := by
  apply nodeValid_prime [2, 43, 27080717] ⟨37263066593, 3, [(2, 5), (43, 1), (27080717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_27080717
  · decide +kernel

theorem prime_76081068233 : Nat.Prime 76081068233 := by
  apply nodeValid_prime [2, 13, 3943, 185531] ⟨76081068233, 3, [(2, 3), (13, 1), (3943, 1), (185531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3943
    · exact prime_185531
  · decide +kernel

theorem prime_94538672413 : Nat.Prime 94538672413 := by
  apply nodeValid_prime [2, 3, 7878222701] ⟨94538672413, 2, [(2, 2), (3, 1), (7878222701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7878222701
  · decide +kernel

theorem prime_105132126031 : Nat.Prime 105132126031 := by
  apply nodeValid_prime [2, 3, 5, 73, 48005537] ⟨105132126031, 6, [(2, 1), (3, 1), (5, 1), (73, 1), (48005537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_73
    · exact prime_48005537
  · decide +kernel

theorem prime_157030271137 : Nat.Prime 157030271137 := by
  apply nodeValid_prime [2, 3, 2083, 87253] ⟨157030271137, 10, [(2, 5), (3, 3), (2083, 1), (87253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2083
    · exact prime_87253
  · decide +kernel

theorem prime_237552049661 : Nat.Prime 237552049661 := by
  apply nodeValid_prime [2, 5, 17, 67, 127, 157, 523] ⟨237552049661, 2, [(2, 2), (5, 1), (17, 1), (67, 1), (127, 1), (157, 1), (523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_67
    · exact prime_127
    · exact prime_157
    · exact prime_523
  · decide +kernel

theorem prime_314327392381 : Nat.Prime 314327392381 := by
  apply nodeValid_prime [2, 3, 5, 3919, 445589] ⟨314327392381, 10, [(2, 2), (3, 2), (5, 1), (3919, 1), (445589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_3919
    · exact prime_445589
  · decide +kernel

theorem prime_941381524987 : Nat.Prime 941381524987 := by
  apply nodeValid_prime [2, 3, 7, 22413845833] ⟨941381524987, 2, [(2, 1), (3, 1), (7, 1), (22413845833, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_22413845833
  · decide +kernel

theorem prime_1893984032543 : Nat.Prime 1893984032543 := by
  apply nodeValid_prime [2, 7, 138581, 139459] ⟨1893984032543, 5, [(2, 1), (7, 2), (138581, 1), (139459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_138581
    · exact prime_139459
  · decide +kernel

theorem prime_1900416397289 : Nat.Prime 1900416397289 := by
  apply nodeValid_prime [2, 237552049661] ⟨1900416397289, 3, [(2, 3), (237552049661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_237552049661
  · decide +kernel

theorem prime_3733622720719 : Nat.Prime 3733622720719 := by
  apply nodeValid_prime [2, 3, 11, 41, 1531, 901213] ⟨3733622720719, 3, [(2, 1), (3, 1), (11, 1), (41, 1), (1531, 1), (901213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_1531
    · exact prime_901213
  · decide +kernel

theorem prime_3733622766541 : Nat.Prime 3733622766541 := by
  apply nodeValid_prime [2, 3, 5, 17, 37, 2203, 14969] ⟨3733622766541, 6, [(2, 2), (3, 2), (5, 1), (17, 1), (37, 1), (2203, 1), (14969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_37
    · exact prime_2203
    · exact prime_14969
  · decide +kernel

theorem prime_3733622767117 : Nat.Prime 3733622767117 := by
  apply nodeValid_prime [2, 3, 11, 173, 6055453] ⟨3733622767117, 2, [(2, 2), (3, 4), (11, 1), (173, 1), (6055453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_173
    · exact prime_6055453
  · decide +kernel

theorem prime_3736804787839 : Nat.Prime 3736804787839 := by
  apply nodeValid_prime [2, 3, 19, 827, 13212007] ⟨3736804787839, 3, [(2, 1), (3, 2), (19, 1), (827, 1), (13212007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_827
    · exact prime_13212007
  · decide +kernel

theorem prime_3736804811323 : Nat.Prime 3736804811323 := by
  apply nodeValid_prime [2, 3, 11, 19, 2979908143] ⟨3736804811323, 2, [(2, 1), (3, 1), (11, 1), (19, 1), (2979908143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_19
    · exact prime_2979908143
  · decide +kernel

theorem prime_3736804812439 : Nat.Prime 3736804812439 := by
  apply nodeValid_prime [2, 3, 151, 193, 21370511] ⟨3736804812439, 6, [(2, 1), (3, 1), (151, 1), (193, 1), (21370511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_193
    · exact prime_21370511
  · decide +kernel

theorem prime_3739988658947 : Nat.Prime 3739988658947 := by
  apply nodeValid_prime [2, 127, 14724364799] ⟨3739988658947, 2, [(2, 1), (127, 1), (14724364799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_14724364799
  · decide +kernel

theorem prime_3739988659157 : Nat.Prime 3739988659157 := by
  apply nodeValid_prime [2, 23, 977, 41609059] ⟨3739988659157, 2, [(2, 2), (23, 1), (977, 1), (41609059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_977
    · exact prime_41609059
  · decide +kernel

theorem prime_3739988689897 : Nat.Prime 3739988689897 := by
  apply nodeValid_prime [2, 3, 3313, 47036783] ⟨3739988689897, 5, [(2, 3), (3, 1), (3313, 1), (47036783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3313
    · exact prime_47036783
  · decide +kernel

theorem prime_3743174428519 : Nat.Prime 3743174428519 := by
  apply nodeValid_prime [2, 3, 7, 103, 865273793] ⟨3743174428519, 6, [(2, 1), (3, 1), (7, 1), (103, 1), (865273793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_865273793
  · decide +kernel

theorem prime_3743174482519 : Nat.Prime 3743174482519 := by
  apply nodeValid_prime [2, 3, 41, 23531, 646643] ⟨3743174482519, 15, [(2, 1), (3, 1), (41, 1), (23531, 1), (646643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_23531
    · exact prime_646643
  · decide +kernel

theorem prime_3743174483647 : Nat.Prime 3743174483647 := by
  apply nodeValid_prime [2, 3, 13, 2347, 20447131] ⟨3743174483647, 3, [(2, 1), (3, 1), (13, 1), (2347, 1), (20447131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2347
    · exact prime_20447131
  · decide +kernel

theorem prime_3746361930517 : Nat.Prime 3746361930517 := by
  apply nodeValid_prime [2, 3, 122449, 849869] ⟨3746361930517, 5, [(2, 2), (3, 2), (122449, 1), (849869, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_122449
    · exact prime_849869
  · decide +kernel

theorem prime_3746361932239 : Nat.Prime 3746361932239 := by
  apply nodeValid_prime [2, 3, 19, 32862823967] ⟨3746361932239, 3, [(2, 1), (3, 1), (19, 1), (32862823967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_32862823967
  · decide +kernel

theorem prime_3746361996893 : Nat.Prime 3746361996893 := by
  apply nodeValid_prime [2, 3571, 262276813] ⟨3746361996893, 2, [(2, 2), (3571, 1), (262276813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3571
    · exact prime_262276813
  · decide +kernel

theorem prime_3749551323521 : Nat.Prime 3749551323521 := by
  apply nodeValid_prime [2, 5, 17, 37, 9314267] ⟨3749551323521, 3, [(2, 7), (5, 1), (17, 1), (37, 1), (9314267, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_37
    · exact prime_9314267
  · decide +kernel

theorem prime_3749551324367 : Nat.Prime 3749551324367 := by
  apply nodeValid_prime [2, 29, 41, 1576766747] ⟨3749551324367, 5, [(2, 1), (29, 1), (41, 1), (1576766747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_41
    · exact prime_1576766747
  · decide +kernel

theorem prime_3749551409777 : Nat.Prime 3749551409777 := by
  apply nodeValid_prime [2, 128747, 1820213] ⟨3749551409777, 3, [(2, 4), (128747, 1), (1820213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_128747
    · exact prime_1820213
  · decide +kernel

theorem prime_3752742616907 : Nat.Prime 3752742616907 := by
  apply nodeValid_prime [2, 212057, 8848429] ⟨3752742616907, 2, [(2, 1), (212057, 1), (8848429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_212057
    · exact prime_8848429
  · decide +kernel

theorem prime_3752742616993 : Nat.Prime 3752742616993 := by
  apply nodeValid_prime [2, 3, 4343452103] ⟨3752742616993, 5, [(2, 5), (3, 3), (4343452103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4343452103
  · decide +kernel

theorem prime_3752742660151 : Nat.Prime 3752742660151 := by
  apply nodeValid_prime [2, 3, 5, 11, 149, 1387669] ⟨3752742660151, 6, [(2, 1), (3, 1), (5, 2), (11, 2), (149, 1), (1387669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_149
    · exact prime_1387669
  · decide +kernel

theorem prime_3755935712873 : Nat.Prime 3755935712873 := by
  apply nodeValid_prime [2, 7, 1129, 1597, 37199] ⟨3755935712873, 3, [(2, 3), (7, 1), (1129, 1), (1597, 1), (37199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1129
    · exact prime_1597
    · exact prime_37199
  · decide +kernel

theorem prime_3755935712989 : Nat.Prime 3755935712989 := by
  apply nodeValid_prime [2, 3, 31, 3365533793] ⟨3755935712989, 2, [(2, 2), (3, 2), (31, 1), (3365533793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_3365533793
  · decide +kernel

theorem prime_3755935751801 : Nat.Prime 3755935751801 := by
  apply nodeValid_prime [2, 5, 31, 605796089] ⟨3755935751801, 15, [(2, 3), (5, 2), (31, 1), (605796089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_605796089
  · decide +kernel

theorem prime_3759130688779 : Nat.Prime 3759130688779 := by
  apply nodeValid_prime [2, 3, 17, 1103, 11137571] ⟨3759130688779, 10, [(2, 1), (3, 2), (17, 1), (1103, 1), (11137571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_1103
    · exact prime_11137571
  · decide +kernel

theorem prime_3759130701901 : Nat.Prime 3759130701901 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 3706133] ⟨3759130701901, 2, [(2, 2), (3, 2), (5, 2), (7, 2), (23, 1), (3706133, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_3706133
  · decide +kernel

theorem prime_3759130704067 : Nat.Prime 3759130704067 := by
  apply nodeValid_prime [2, 3, 246131, 2545481] ⟨3759130704067, 2, [(2, 1), (3, 1), (246131, 1), (2545481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_246131
    · exact prime_2545481
  · decide +kernel

theorem prime_3762327473351 : Nat.Prime 3762327473351 := by
  apply nodeValid_prime [2, 5, 1277, 58924471] ⟨3762327473351, 13, [(2, 1), (5, 2), (1277, 1), (58924471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1277
    · exact prime_58924471
  · decide +kernel

theorem prime_3762327489419 : Nat.Prime 3762327489419 := by
  apply nodeValid_prime [2, 43, 2339, 18703717] ⟨3762327489419, 2, [(2, 1), (43, 1), (2339, 1), (18703717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_2339
    · exact prime_18703717
  · decide +kernel

theorem prime_3762327497267 : Nat.Prime 3762327497267 := by
  apply nodeValid_prime [2, 13, 211, 685805231] ⟨3762327497267, 2, [(2, 1), (13, 1), (211, 1), (685805231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_211
    · exact prime_685805231
  · decide +kernel

theorem prime_3765526099949 : Nat.Prime 3765526099949 := by
  apply nodeValid_prime [2, 941381524987] ⟨3765526099949, 2, [(2, 2), (941381524987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_941381524987
  · decide +kernel

theorem prime_3765526141009 : Nat.Prime 3765526141009 := by
  apply nodeValid_prime [2, 3, 37, 12281, 172643] ⟨3765526141009, 7, [(2, 4), (3, 1), (37, 1), (12281, 1), (172643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_12281
    · exact prime_172643
  · decide +kernel

theorem prime_3765526141301 : Nat.Prime 3765526141301 := by
  apply nodeValid_prime [2, 5, 7, 11, 489029369] ⟨3765526141301, 2, [(2, 2), (5, 2), (7, 1), (11, 1), (489029369, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_489029369
  · decide +kernel

theorem prime_3768726504463 : Nat.Prime 3768726504463 := by
  apply nodeValid_prime [2, 3, 53, 109, 193, 563357] ⟨3768726504463, 3, [(2, 1), (3, 1), (53, 1), (109, 1), (193, 1), (563357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_109
    · exact prime_193
    · exact prime_563357
  · decide +kernel

theorem prime_3768726507289 : Nat.Prime 3768726507289 := by
  apply nodeValid_prime [2, 3, 157030271137] ⟨3768726507289, 17, [(2, 3), (3, 1), (157030271137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157030271137
  · decide +kernel

theorem prime_3768726569911 : Nat.Prime 3768726569911 := by
  apply nodeValid_prime [2, 3, 5, 17, 397, 18613753] ⟨3768726569911, 6, [(2, 1), (3, 1), (5, 1), (17, 1), (397, 1), (18613753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_397
    · exact prime_18613753
  · decide +kernel

theorem prime_3771928708573 : Nat.Prime 3771928708573 := by
  apply nodeValid_prime [2, 3, 314327392381] ⟨3771928708573, 5, [(2, 2), (3, 1), (314327392381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_314327392381
  · decide +kernel

theorem prime_3771928708687 : Nat.Prime 3771928708687 := by
  apply nodeValid_prime [2, 3, 13339, 15709693] ⟨3771928708687, 3, [(2, 1), (3, 2), (13339, 1), (15709693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13339
    · exact prime_15709693
  · decide +kernel

theorem prime_3771928884179 : Nat.Prime 3771928884179 := by
  apply nodeValid_prime [2, 7, 13, 20724883979] ⟨3771928884179, 2, [(2, 1), (7, 1), (13, 1), (20724883979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_20724883979
  · decide +kernel

theorem prime_3775133004007 : Nat.Prime 3775133004007 := by
  apply nodeValid_prime [2, 3, 7, 13, 179, 1373, 4019] ⟨3775133004007, 5, [(2, 1), (3, 1), (7, 2), (13, 1), (179, 1), (1373, 1), (4019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_179
    · exact prime_1373
    · exact prime_4019
  · decide +kernel

theorem prime_3775133004101 : Nat.Prime 3775133004101 := by
  apply nodeValid_prime [2, 5, 17, 2220666473] ⟨3775133004101, 2, [(2, 2), (5, 2), (17, 1), (2220666473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2220666473
  · decide +kernel

theorem prime_3775133034433 : Nat.Prime 3775133034433 := by
  apply nodeValid_prime [2, 3, 47, 15494209] ⟨3775133034433, 5, [(2, 6), (3, 4), (47, 1), (15494209, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_15494209
  · decide +kernel

theorem prime_3778338918659 : Nat.Prime 3778338918659 := by
  apply nodeValid_prime [2, 163, 11589996683] ⟨3778338918659, 2, [(2, 1), (163, 1), (11589996683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_163
    · exact prime_11589996683
  · decide +kernel

theorem prime_3778338919193 : Nat.Prime 3778338919193 := by
  apply nodeValid_prime [2, 6733, 70145903] ⟨3778338919193, 3, [(2, 3), (6733, 1), (70145903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6733
    · exact prime_70145903
  · decide +kernel

theorem prime_3778339024717 : Nat.Prime 3778339024717 := by
  apply nodeValid_prime [2, 3, 17, 43, 430727203] ⟨3778339024717, 5, [(2, 2), (3, 1), (17, 1), (43, 1), (430727203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_43
    · exact prime_430727203
  · decide +kernel

theorem prime_3781546857799 : Nat.Prime 3781546857799 := by
  apply nodeValid_prime [2, 3, 101, 733, 8513201] ⟨3781546857799, 7, [(2, 1), (3, 1), (101, 1), (733, 1), (8513201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_733
    · exact prime_8513201
  · decide +kernel

theorem prime_3781546895939 : Nat.Prime 3781546895939 := by
  apply nodeValid_prime [2, 7, 131, 2061912157] ⟨3781546895939, 2, [(2, 1), (7, 1), (131, 1), (2061912157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_131
    · exact prime_2061912157
  · decide +kernel

theorem prime_3781546896521 : Nat.Prime 3781546896521 := by
  apply nodeValid_prime [2, 5, 94538672413] ⟨3781546896521, 3, [(2, 3), (5, 1), (94538672413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_94538672413
  · decide +kernel

theorem prime_3784756515667 : Nat.Prime 3784756515667 := by
  apply nodeValid_prime [2, 3, 7, 54167, 1663619] ⟨3784756515667, 3, [(2, 1), (3, 1), (7, 1), (54167, 1), (1663619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_54167
    · exact prime_1663619
  · decide +kernel

theorem prime_3784756515697 : Nat.Prime 3784756515697 := by
  apply nodeValid_prime [2, 3, 13, 673923881] ⟨3784756515697, 7, [(2, 4), (3, 3), (13, 1), (673923881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_673923881
  · decide +kernel

theorem prime_3784756537117 : Nat.Prime 3784756537117 := by
  apply nodeValid_prime [2, 3, 105132126031] ⟨3784756537117, 2, [(2, 2), (3, 2), (105132126031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105132126031
  · decide +kernel

theorem prime_3787968049519 : Nat.Prime 3787968049519 := by
  apply nodeValid_prime [2, 3, 431, 1464798163] ⟨3787968049519, 6, [(2, 1), (3, 1), (431, 1), (1464798163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_431
    · exact prime_1464798163
  · decide +kernel

theorem prime_3787968050171 : Nat.Prime 3787968050171 := by
  apply nodeValid_prime [2, 5, 17, 73, 305235137] ⟨3787968050171, 2, [(2, 1), (5, 1), (17, 1), (73, 1), (305235137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_73
    · exact prime_305235137
  · decide +kernel

theorem prime_3787968065087 : Nat.Prime 3787968065087 := by
  apply nodeValid_prime [2, 1893984032543] ⟨3787968065087, 5, [(2, 1), (1893984032543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1893984032543
  · decide +kernel

theorem prime_3791181335083 : Nat.Prime 3791181335083 := by
  apply nodeValid_prime [2, 3, 67, 9430799341] ⟨3791181335083, 2, [(2, 1), (3, 1), (67, 1), (9430799341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_9430799341
  · decide +kernel

theorem prime_3791181444593 : Nat.Prime 3791181444593 := by
  apply nodeValid_prime [2, 31, 41, 7951, 23447] ⟨3791181444593, 3, [(2, 4), (31, 1), (41, 1), (7951, 1), (23447, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41
    · exact prime_7951
    · exact prime_23447
  · decide +kernel

theorem prime_3794396604107 : Nat.Prime 3794396604107 := by
  apply nodeValid_prime [2, 5273, 359794861] ⟨3794396604107, 2, [(2, 1), (5273, 1), (359794861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5273
    · exact prime_359794861
  · decide +kernel

theorem prime_3794396604689 : Nat.Prime 3794396604689 := by
  apply nodeValid_prime [2, 419, 601, 941747] ⟨3794396604689, 3, [(2, 4), (419, 1), (601, 1), (941747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_419
    · exact prime_601
    · exact prime_941747
  · decide +kernel

theorem prime_3794396664217 : Nat.Prime 3794396664217 := by
  apply nodeValid_prime [2, 3, 641, 246645649] ⟨3794396664217, 5, [(2, 3), (3, 1), (641, 1), (246645649, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_641
    · exact prime_246645649
  · decide +kernel

theorem prime_3797613733103 : Nat.Prime 3797613733103 := by
  apply nodeValid_prime [2, 7, 71963, 3769411] ⟨3797613733103, 7, [(2, 1), (7, 1), (71963, 1), (3769411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_71963
    · exact prime_3769411
  · decide +kernel

theorem prime_3797613740443 : Nat.Prime 3797613740443 := by
  apply nodeValid_prime [2, 3, 9137, 69271711] ⟨3797613740443, 3, [(2, 1), (3, 1), (9137, 1), (69271711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9137
    · exact prime_69271711
  · decide +kernel

theorem prime_3797613741403 : Nat.Prime 3797613741403 := by
  apply nodeValid_prime [2, 3, 13, 661, 24552373] ⟨3797613741403, 11, [(2, 1), (3, 2), (13, 1), (661, 1), (24552373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_661
    · exact prime_24552373
  · decide +kernel

theorem prime_3800832655079 : Nat.Prime 3800832655079 := by
  apply nodeValid_prime [2, 37, 193, 266127479] ⟨3800832655079, 11, [(2, 1), (37, 1), (193, 1), (266127479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_193
    · exact prime_266127479
  · decide +kernel

theorem prime_3800832792487 : Nat.Prime 3800832792487 := by
  apply nodeValid_prime [2, 3, 17, 37263066593] ⟨3800832792487, 6, [(2, 1), (3, 1), (17, 1), (37263066593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37263066593
  · decide +kernel

theorem prime_3800832794579 : Nat.Prime 3800832794579 := by
  apply nodeValid_prime [2, 1900416397289] ⟨3800832794579, 2, [(2, 1), (1900416397289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1900416397289
  · decide +kernel

theorem prime_3804053409383 : Nat.Prime 3804053409383 := by
  apply nodeValid_prime [2, 1063, 15073, 118709] ⟨3804053409383, 5, [(2, 1), (1063, 1), (15073, 1), (118709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1063
    · exact prime_15073
    · exact prime_118709
  · decide +kernel

theorem prime_3804053411651 : Nat.Prime 3804053411651 := by
  apply nodeValid_prime [2, 5, 76081068233] ⟨3804053411651, 2, [(2, 1), (5, 2), (76081068233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_76081068233
  · decide +kernel

theorem prime_3804053417833 : Nat.Prime 3804053417833 := by
  apply nodeValid_prime [2, 3, 37, 4283843939] ⟨3804053417833, 5, [(2, 3), (3, 1), (37, 1), (4283843939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_4283843939
  · decide +kernel

theorem prime_3807275976557 : Nat.Prime 3807275976557 := by
  apply nodeValid_prime [2, 13, 15919, 4599337] ⟨3807275976557, 2, [(2, 2), (13, 1), (15919, 1), (4599337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_15919
    · exact prime_4599337
  · decide +kernel

theorem prime_3807275976671 : Nat.Prime 3807275976671 := by
  apply nodeValid_prime [2, 5, 106411, 3577897] ⟨3807275976671, 13, [(2, 1), (5, 1), (106411, 1), (3577897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_106411
    · exact prime_3577897
  · decide +kernel

theorem prime_3807276011761 : Nat.Prime 3807276011761 := by
  apply nodeValid_prime [2, 3, 5, 13, 157, 229, 33941] ⟨3807276011761, 19, [(2, 4), (3, 1), (5, 1), (13, 1), (157, 1), (229, 1), (33941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_157
    · exact prime_229
    · exact prime_33941
  · decide +kernel

theorem prime_3810500417467 : Nat.Prime 3810500417467 := by
  apply nodeValid_prime [2, 3, 3947, 4999, 10729] ⟨3810500417467, 3, [(2, 1), (3, 2), (3947, 1), (4999, 1), (10729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3947
    · exact prime_4999
    · exact prime_10729
  · decide +kernel

theorem prime_3810500418607 : Nat.Prime 3810500418607 := by
  apply nodeValid_prime [2, 3, 7, 79, 1277, 899321] ⟨3810500418607, 3, [(2, 1), (3, 1), (7, 1), (79, 1), (1277, 1), (899321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_1277
    · exact prime_899321
  · decide +kernel

theorem prime_3810500454763 : Nat.Prime 3810500454763 := by
  apply nodeValid_prime [2, 3, 41, 5163279749] ⟨3810500454763, 3, [(2, 1), (3, 2), (41, 1), (5163279749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_5163279749
  · decide +kernel

end Sude.Lucas.Generated
