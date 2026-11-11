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
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0038
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0040
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0050
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0054
import Sude.GeneratedFTT.N0061
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0067
import Sude.GeneratedFTT.N0069
import Sude.GeneratedFTT.N0073
import Sude.GeneratedFTT.N0077
import Sude.GeneratedFTT.N0078
import Sude.GeneratedFTT.N0085
import Sude.GeneratedFTT.N0088
import Sude.GeneratedFTT.N0099
import Sude.GeneratedFTT.N0100
import Sude.GeneratedFTT.N0103
import Sude.GeneratedFTT.N0107
import Sude.GeneratedFTT.N0119
import Sude.GeneratedFTT.N0121

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_16127 : Nat.Prime 16127 := by
  apply nodeValid_prime [2, 11, 733] ⟨16127, 5, [(2, 1), (11, 1), (733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_733
  · decide +kernel

theorem prime_17299 : Nat.Prime 17299 := by
  apply nodeValid_prime [2, 3, 31] ⟨17299, 2, [(2, 1), (3, 2), (31, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_17317 : Nat.Prime 17317 := by
  apply nodeValid_prime [2, 3, 13, 37] ⟨17317, 2, [(2, 2), (3, 2), (13, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_37
  · decide +kernel

theorem prime_20129 : Nat.Prime 20129 := by
  apply nodeValid_prime [2, 17, 37] ⟨20129, 3, [(2, 5), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_20549 : Nat.Prime 20549 := by
  apply nodeValid_prime [2, 11, 467] ⟨20549, 2, [(2, 2), (11, 1), (467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_467
  · decide +kernel

theorem prime_21391 : Nat.Prime 21391 := by
  apply nodeValid_prime [2, 3, 5, 23, 31] ⟨21391, 6, [(2, 1), (3, 1), (5, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_21433 : Nat.Prime 21433 := by
  apply nodeValid_prime [2, 3, 19, 47] ⟨21433, 5, [(2, 3), (3, 1), (19, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_47
  · decide +kernel

theorem prime_21493 : Nat.Prime 21493 := by
  apply nodeValid_prime [2, 3, 199] ⟨21493, 2, [(2, 2), (3, 3), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
  · decide +kernel

theorem prime_24023 : Nat.Prime 24023 := by
  apply nodeValid_prime [2, 12011] ⟨24023, 5, [(2, 1), (12011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_12011
  · decide +kernel

theorem prime_24733 : Nat.Prime 24733 := by
  apply nodeValid_prime [2, 3, 229] ⟨24733, 2, [(2, 2), (3, 3), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_229
  · decide +kernel

theorem prime_29063 : Nat.Prime 29063 := by
  apply nodeValid_prime [2, 11, 1321] ⟨29063, 10, [(2, 1), (11, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1321
  · decide +kernel

theorem prime_30851 : Nat.Prime 30851 := by
  apply nodeValid_prime [2, 5, 617] ⟨30851, 2, [(2, 1), (5, 2), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_617
  · decide +kernel

theorem prime_36599 : Nat.Prime 36599 := by
  apply nodeValid_prime [2, 29, 631] ⟨36599, 19, [(2, 1), (29, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_631
  · decide +kernel

theorem prime_36793 : Nat.Prime 36793 := by
  apply nodeValid_prime [2, 3, 7, 73] ⟨36793, 15, [(2, 3), (3, 2), (7, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_73
  · decide +kernel

theorem prime_40693 : Nat.Prime 40693 := by
  apply nodeValid_prime [2, 3, 3391] ⟨40693, 2, [(2, 2), (3, 1), (3391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3391
  · decide +kernel

theorem prime_48907 : Nat.Prime 48907 := by
  apply nodeValid_prime [2, 3, 11, 13, 19] ⟨48907, 2, [(2, 1), (3, 2), (11, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_51419 : Nat.Prime 51419 := by
  apply nodeValid_prime [2, 47, 547] ⟨51419, 2, [(2, 1), (47, 1), (547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_547
  · decide +kernel

theorem prime_54917 : Nat.Prime 54917 := by
  apply nodeValid_prime [2, 13729] ⟨54917, 2, [(2, 2), (13729, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13729
  · decide +kernel

theorem prime_60397 : Nat.Prime 60397 := by
  apply nodeValid_prime [2, 3, 7, 719] ⟨60397, 5, [(2, 2), (3, 1), (7, 1), (719, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_719
  · decide +kernel

theorem prime_61703 : Nat.Prime 61703 := by
  apply nodeValid_prime [2, 30851] ⟨61703, 5, [(2, 1), (30851, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_30851
  · decide +kernel

theorem prime_63127 : Nat.Prime 63127 := by
  apply nodeValid_prime [2, 3, 7, 167] ⟨63127, 3, [(2, 1), (3, 3), (7, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_167
  · decide +kernel

theorem prime_63281 : Nat.Prime 63281 := by
  apply nodeValid_prime [2, 5, 7, 113] ⟨63281, 6, [(2, 4), (5, 1), (7, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_113
  · decide +kernel

theorem prime_68813 : Nat.Prime 68813 := by
  apply nodeValid_prime [2, 17203] ⟨68813, 2, [(2, 2), (17203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17203
  · decide +kernel

theorem prime_68891 : Nat.Prime 68891 := by
  apply nodeValid_prime [2, 5, 83] ⟨68891, 2, [(2, 1), (5, 1), (83, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_83
  · decide +kernel

theorem prime_97973 : Nat.Prime 97973 := by
  apply nodeValid_prime [2, 7, 3499] ⟨97973, 2, [(2, 2), (7, 1), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3499
  · decide +kernel

theorem prime_99881 : Nat.Prime 99881 := by
  apply nodeValid_prime [2, 5, 11, 227] ⟨99881, 6, [(2, 3), (5, 1), (11, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_227
  · decide +kernel

theorem prime_103903 : Nat.Prime 103903 := by
  apply nodeValid_prime [2, 3, 17317] ⟨103903, 3, [(2, 1), (3, 1), (17317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17317
  · decide +kernel

theorem prime_109481 : Nat.Prime 109481 := by
  apply nodeValid_prime [2, 5, 7, 17, 23] ⟨109481, 3, [(2, 3), (5, 1), (7, 1), (17, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_23
  · decide +kernel

theorem prime_110927 : Nat.Prime 110927 := by
  apply nodeValid_prime [2, 37, 1499] ⟨110927, 10, [(2, 1), (37, 1), (1499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_1499
  · decide +kernel

theorem prime_114113 : Nat.Prime 114113 := by
  apply nodeValid_prime [2, 1783] ⟨114113, 3, [(2, 6), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1783
  · decide +kernel

theorem prime_125737 : Nat.Prime 125737 := by
  apply nodeValid_prime [2, 3, 13, 31] ⟨125737, 5, [(2, 3), (3, 1), (13, 2), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_31
  · decide +kernel

theorem prime_137791 : Nat.Prime 137791 := by
  apply nodeValid_prime [2, 3, 5, 1531] ⟨137791, 3, [(2, 1), (3, 2), (5, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1531
  · decide +kernel

theorem prime_145723 : Nat.Prime 145723 := by
  apply nodeValid_prime [2, 3, 149, 163] ⟨145723, 3, [(2, 1), (3, 1), (149, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
    · exact prime_163
  · decide +kernel

theorem prime_158009 : Nat.Prime 158009 := by
  apply nodeValid_prime [2, 19751] ⟨158009, 3, [(2, 3), (19751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19751
  · decide +kernel

theorem prime_162493 : Nat.Prime 162493 := by
  apply nodeValid_prime [2, 3, 11, 1231] ⟨162493, 5, [(2, 2), (3, 1), (11, 1), (1231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1231
  · decide +kernel

theorem prime_197083 : Nat.Prime 197083 := by
  apply nodeValid_prime [2, 3, 10949] ⟨197083, 2, [(2, 1), (3, 2), (10949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10949
  · decide +kernel

theorem prime_215143 : Nat.Prime 215143 := by
  apply nodeValid_prime [2, 3, 23, 1559] ⟨215143, 5, [(2, 1), (3, 1), (23, 1), (1559, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_1559
  · decide +kernel

theorem prime_241589 : Nat.Prime 241589 := by
  apply nodeValid_prime [2, 60397] ⟨241589, 2, [(2, 2), (60397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_60397
  · decide +kernel

theorem prime_281807 : Nat.Prime 281807 := by
  apply nodeValid_prime [2, 7, 20129] ⟨281807, 7, [(2, 1), (7, 1), (20129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_20129
  · decide +kernel

theorem prime_311737 : Nat.Prime 311737 := by
  apply nodeValid_prime [2, 3, 31, 419] ⟨311737, 5, [(2, 3), (3, 1), (31, 1), (419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_419
  · decide +kernel

theorem prime_343303 : Nat.Prime 343303 := by
  apply nodeValid_prime [2, 3, 29, 1973] ⟨343303, 3, [(2, 1), (3, 1), (29, 1), (1973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1973
  · decide +kernel

theorem prime_528863 : Nat.Prime 528863 := by
  apply nodeValid_prime [2, 23, 11497] ⟨528863, 5, [(2, 1), (23, 1), (11497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_11497
  · decide +kernel

theorem prime_588151 : Nat.Prime 588151 := by
  apply nodeValid_prime [2, 3, 5, 1307] ⟨588151, 3, [(2, 1), (3, 2), (5, 2), (1307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1307
  · decide +kernel

theorem prime_709589 : Nat.Prime 709589 := by
  apply nodeValid_prime [2, 11, 16127] ⟨709589, 2, [(2, 2), (11, 1), (16127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_16127
  · decide +kernel

theorem prime_761249 : Nat.Prime 761249 := by
  apply nodeValid_prime [2, 23789] ⟨761249, 3, [(2, 5), (23789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23789
  · decide +kernel

theorem prime_792179 : Nat.Prime 792179 := by
  apply nodeValid_prime [2, 431, 919] ⟨792179, 2, [(2, 1), (431, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_431
    · exact prime_919
  · decide +kernel

theorem prime_840923 : Nat.Prime 840923 := by
  apply nodeValid_prime [2, 17, 24733] ⟨840923, 2, [(2, 1), (17, 1), (24733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_24733
  · decide +kernel

theorem prime_867733 : Nat.Prime 867733 := by
  apply nodeValid_prime [2, 3, 167, 433] ⟨867733, 5, [(2, 2), (3, 1), (167, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_433
  · decide +kernel

theorem prime_1010033 : Nat.Prime 1010033 := by
  apply nodeValid_prime [2, 63127] ⟨1010033, 3, [(2, 4), (63127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_63127
  · decide +kernel

theorem prime_1211689 : Nat.Prime 1211689 := by
  apply nodeValid_prime [2, 3, 16829] ⟨1211689, 11, [(2, 3), (3, 2), (16829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_16829
  · decide +kernel

theorem prime_1282681 : Nat.Prime 1282681 := by
  apply nodeValid_prime [2, 3, 5, 7, 509] ⟨1282681, 19, [(2, 3), (3, 2), (5, 1), (7, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_509
  · decide +kernel

theorem prime_1419179 : Nat.Prime 1419179 := by
  apply nodeValid_prime [2, 709589] ⟨1419179, 2, [(2, 1), (709589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_709589
  · decide +kernel

theorem prime_1651513 : Nat.Prime 1651513 := by
  apply nodeValid_prime [2, 3, 68813] ⟨1651513, 7, [(2, 3), (3, 1), (68813, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_68813
  · decide +kernel

theorem prime_1925191 : Nat.Prime 1925191 := by
  apply nodeValid_prime [2, 3, 5, 21391] ⟨1925191, 6, [(2, 1), (3, 2), (5, 1), (21391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21391
  · decide +kernel

theorem prime_1941763 : Nat.Prime 1941763 := by
  apply nodeValid_prime [2, 3, 19, 17033] ⟨1941763, 2, [(2, 1), (3, 1), (19, 1), (17033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_17033
  · decide +kernel

theorem prime_1976347 : Nat.Prime 1976347 := by
  apply nodeValid_prime [2, 3, 36599] ⟨1976347, 2, [(2, 1), (3, 3), (36599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_36599
  · decide +kernel

theorem prime_2342797 : Nat.Prime 2342797 := by
  apply nodeValid_prime [2, 3, 101, 1933] ⟨2342797, 11, [(2, 2), (3, 1), (101, 1), (1933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_1933
  · decide +kernel

theorem prime_2393837 : Nat.Prime 2393837 := by
  apply nodeValid_prime [2, 71, 8429] ⟨2393837, 2, [(2, 2), (71, 1), (8429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_8429
  · decide +kernel

theorem prime_2897357 : Nat.Prime 2897357 := by
  apply nodeValid_prime [2, 7, 11, 23, 409] ⟨2897357, 2, [(2, 2), (7, 1), (11, 1), (23, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_23
    · exact prime_409
  · decide +kernel

theorem prime_2898739 : Nat.Prime 2898739 := by
  apply nodeValid_prime [2, 3, 17, 9473] ⟨2898739, 3, [(2, 1), (3, 2), (17, 1), (9473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_9473
  · decide +kernel

theorem prime_3090613 : Nat.Prime 3090613 := by
  apply nodeValid_prime [2, 3, 7, 36793] ⟨3090613, 2, [(2, 2), (3, 1), (7, 1), (36793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_36793
  · decide +kernel

theorem prime_3187979 : Nat.Prime 3187979 := by
  apply nodeValid_prime [2, 31, 51419] ⟨3187979, 2, [(2, 1), (31, 1), (51419, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_51419
  · decide +kernel

theorem prime_3528907 : Nat.Prime 3528907 := by
  apply nodeValid_prime [2, 3, 588151] ⟨3528907, 2, [(2, 1), (3, 1), (588151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_588151
  · decide +kernel

theorem prime_3616409 : Nat.Prime 3616409 := by
  apply nodeValid_prime [2, 251, 1801] ⟨3616409, 3, [(2, 3), (251, 1), (1801, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_1801
  · decide +kernel

theorem prime_3701783 : Nat.Prime 3701783 := by
  apply nodeValid_prime [2, 7, 79, 3347] ⟨3701783, 7, [(2, 1), (7, 1), (79, 1), (3347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_3347
  · decide +kernel

theorem prime_4057589 : Nat.Prime 4057589 := by
  apply nodeValid_prime [2, 1014397] ⟨4057589, 2, [(2, 2), (1014397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1014397
  · decide +kernel

theorem prime_4216591 : Nat.Prime 4216591 := by
  apply nodeValid_prime [2, 3, 5, 7, 23, 97] ⟨4216591, 7, [(2, 1), (3, 3), (5, 1), (7, 1), (23, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_97
  · decide +kernel

theorem prime_5045539 : Nat.Prime 5045539 := by
  apply nodeValid_prime [2, 3, 840923] ⟨5045539, 2, [(2, 1), (3, 1), (840923, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_840923
  · decide +kernel

theorem prime_5093029 : Nat.Prime 5093029 := by
  apply nodeValid_prime [2, 3, 23, 6151] ⟨5093029, 2, [(2, 2), (3, 2), (23, 1), (6151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_6151
  · decide +kernel

theorem prime_6687097 : Nat.Prime 6687097 := by
  apply nodeValid_prime [2, 3, 13, 21433] ⟨6687097, 10, [(2, 3), (3, 1), (13, 1), (21433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_21433
  · decide +kernel

theorem prime_9064877 : Nat.Prime 9064877 := by
  apply nodeValid_prime [2, 17, 109, 1223] ⟨9064877, 2, [(2, 2), (17, 1), (109, 1), (1223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_109
    · exact prime_1223
  · decide +kernel

theorem prime_12852617 : Nat.Prime 12852617 := by
  apply nodeValid_prime [2, 7, 37, 6203] ⟨12852617, 3, [(2, 3), (7, 1), (37, 1), (6203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_6203
  · decide +kernel

theorem prime_13592021 : Nat.Prime 13592021 := by
  apply nodeValid_prime [2, 5, 13, 61, 857] ⟨13592021, 10, [(2, 2), (5, 1), (13, 1), (61, 1), (857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_61
    · exact prime_857
  · decide +kernel

theorem prime_20474119 : Nat.Prime 20474119 := by
  apply nodeValid_prime [2, 3, 7, 162493] ⟨20474119, 3, [(2, 1), (3, 2), (7, 1), (162493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_162493
  · decide +kernel

theorem prime_26260859 : Nat.Prime 26260859 := by
  apply nodeValid_prime [2, 13, 1010033] ⟨26260859, 7, [(2, 1), (13, 1), (1010033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1010033
  · decide +kernel

theorem prime_26657159 : Nat.Prime 26657159 := by
  apply nodeValid_prime [2, 11, 1211689] ⟨26657159, 11, [(2, 1), (11, 1), (1211689, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1211689
  · decide +kernel

theorem prime_30329641 : Nat.Prime 30329641 := by
  apply nodeValid_prime [2, 3, 5, 11, 23, 37] ⟨30329641, 14, [(2, 3), (3, 4), (5, 1), (11, 1), (23, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_37
  · decide +kernel

theorem prime_30595241 : Nat.Prime 30595241 := by
  apply nodeValid_prime [2, 5, 13, 17, 3461] ⟨30595241, 3, [(2, 3), (5, 1), (13, 1), (17, 1), (3461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_3461
  · decide +kernel

theorem prime_31300481 : Nat.Prime 31300481 := by
  apply nodeValid_prime [2, 5, 48907] ⟨31300481, 3, [(2, 7), (5, 1), (48907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_48907
  · decide +kernel

theorem prime_33160067 : Nat.Prime 33160067 := by
  apply nodeValid_prime [2, 23, 37, 19483] ⟨33160067, 2, [(2, 1), (23, 1), (37, 1), (19483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_37
    · exact prime_19483
  · decide +kernel

theorem prime_34667197 : Nat.Prime 34667197 := by
  apply nodeValid_prime [2, 3, 167, 17299] ⟨34667197, 5, [(2, 2), (3, 1), (167, 1), (17299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_167
    · exact prime_17299
  · decide +kernel

theorem prime_35327021 : Nat.Prime 35327021 := by
  apply nodeValid_prime [2, 5, 17, 103903] ⟨35327021, 2, [(2, 2), (5, 1), (17, 1), (103903, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_103903
  · decide +kernel

theorem prime_39623761 : Nat.Prime 39623761 := by
  apply nodeValid_prime [2, 3, 5, 11, 5003] ⟨39623761, 19, [(2, 4), (3, 2), (5, 1), (11, 1), (5003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_5003
  · decide +kernel

theorem prime_115630477 : Nat.Prime 115630477 := by
  apply nodeValid_prime [2, 3, 13, 23, 37, 67] ⟨115630477, 2, [(2, 2), (3, 1), (13, 2), (23, 1), (37, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_23
    · exact prime_37
    · exact prime_67
  · decide +kernel

theorem prime_158605987 : Nat.Prime 158605987 := by
  apply nodeValid_prime [2, 3, 7, 11, 343303] ⟨158605987, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (343303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_343303
  · decide +kernel

theorem prime_574470913 : Nat.Prime 574470913 := by
  apply nodeValid_prime [2, 3, 197, 3797] ⟨574470913, 15, [(2, 8), (3, 1), (197, 1), (3797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_3797
  · decide +kernel

theorem prime_616581937 : Nat.Prime 616581937 := by
  apply nodeValid_prime [2, 3, 107, 13339] ⟨616581937, 7, [(2, 4), (3, 3), (107, 1), (13339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_13339
  · decide +kernel

theorem prime_629303111 : Nat.Prime 629303111 := by
  apply nodeValid_prime [2, 5, 17, 3701783] ⟨629303111, 19, [(2, 1), (5, 1), (17, 1), (3701783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_3701783
  · decide +kernel

theorem prime_658856659 : Nat.Prime 658856659 := by
  apply nodeValid_prime [2, 3, 17, 59, 109481] ⟨658856659, 3, [(2, 1), (3, 1), (17, 1), (59, 1), (109481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_59
    · exact prime_109481
  · decide +kernel

theorem prime_666367381 : Nat.Prime 666367381 := by
  apply nodeValid_prime [2, 3, 5, 7, 528863] ⟨666367381, 10, [(2, 2), (3, 2), (5, 1), (7, 1), (528863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_528863
  · decide +kernel

theorem prime_698393543 : Nat.Prime 698393543 := by
  apply nodeValid_prime [2, 7, 11, 211, 21493] ⟨698393543, 7, [(2, 1), (7, 1), (11, 1), (211, 1), (21493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_211
    · exact prime_21493
  · decide +kernel

theorem prime_798604403 : Nat.Prime 798604403 := by
  apply nodeValid_prime [2, 337, 409, 2897] ⟨798604403, 2, [(2, 1), (337, 1), (409, 1), (2897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_337
    · exact prime_409
    · exact prime_2897
  · decide +kernel

theorem prime_864542297 : Nat.Prime 864542297 := by
  apply nodeValid_prime [2, 37, 2920751] ⟨864542297, 3, [(2, 3), (37, 1), (2920751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2920751
  · decide +kernel

theorem prime_1587613543 : Nat.Prime 1587613543 := by
  apply nodeValid_prime [2, 3, 83, 3187979] ⟨1587613543, 5, [(2, 1), (3, 1), (83, 1), (3187979, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_3187979
  · decide +kernel

theorem prime_1866275189 : Nat.Prime 1866275189 := by
  apply nodeValid_prime [2, 563, 857, 967] ⟨1866275189, 2, [(2, 2), (563, 1), (857, 1), (967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_563
    · exact prime_857
    · exact prime_967
  · decide +kernel

theorem prime_2524055539 : Nat.Prime 2524055539 := by
  apply nodeValid_prime [2, 3, 43, 71, 137791] ⟨2524055539, 3, [(2, 1), (3, 1), (43, 1), (71, 1), (137791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_71
    · exact prime_137791
  · decide +kernel

theorem prime_2609898931 : Nat.Prime 2609898931 := by
  apply nodeValid_prime [2, 3, 5, 199, 145723] ⟨2609898931, 2, [(2, 1), (3, 2), (5, 1), (199, 1), (145723, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_199
    · exact prime_145723
  · decide +kernel

theorem prime_2865996491 : Nat.Prime 2865996491 := by
  apply nodeValid_prime [2, 5, 7, 647, 63281] ⟨2865996491, 2, [(2, 1), (5, 1), (7, 1), (647, 1), (63281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_647
    · exact prime_63281
  · decide +kernel

theorem prime_3049250023 : Nat.Prime 3049250023 := by
  apply nodeValid_prime [2, 3, 7, 13, 68947] ⟨3049250023, 7, [(2, 1), (3, 5), (7, 1), (13, 1), (68947, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_68947
  · decide +kernel

theorem prime_3334136297 : Nat.Prime 3334136297 := by
  apply nodeValid_prime [2, 53, 167, 47087] ⟨3334136297, 3, [(2, 3), (53, 1), (167, 1), (47087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_167
    · exact prime_47087
  · decide +kernel

theorem prime_3881185057 : Nat.Prime 3881185057 := by
  apply nodeValid_prime [2, 3, 7, 1925191] ⟨3881185057, 11, [(2, 5), (3, 2), (7, 1), (1925191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1925191
  · decide +kernel

theorem prime_6663673811 : Nat.Prime 6663673811 := by
  apply nodeValid_prime [2, 5, 666367381] ⟨6663673811, 2, [(2, 1), (5, 1), (666367381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_666367381
  · decide +kernel

theorem prime_8056043659 : Nat.Prime 8056043659 := by
  apply nodeValid_prime [2, 3, 13, 2269, 15173] ⟨8056043659, 2, [(2, 1), (3, 2), (13, 1), (2269, 1), (15173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2269
    · exact prime_15173
  · decide +kernel

theorem prime_11616967667 : Nat.Prime 11616967667 := by
  apply nodeValid_prime [2, 2939, 1976347] ⟨11616967667, 2, [(2, 1), (2939, 1), (1976347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2939
    · exact prime_1976347
  · decide +kernel

theorem prime_13327347623 : Nat.Prime 13327347623 := by
  apply nodeValid_prime [2, 6663673811] ⟨13327347623, 5, [(2, 1), (6663673811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6663673811
  · decide +kernel

theorem prime_15200987317 : Nat.Prime 15200987317 := by
  apply nodeValid_prime [2, 3, 19, 23, 2898739] ⟨15200987317, 2, [(2, 2), (3, 1), (19, 1), (23, 1), (2898739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_23
    · exact prime_2898739
  · decide +kernel

theorem prime_15913467431 : Nat.Prime 15913467431 := by
  apply nodeValid_prime [2, 5, 7, 941, 241589] ⟨15913467431, 14, [(2, 1), (5, 1), (7, 1), (941, 1), (241589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_941
    · exact prime_241589
  · decide +kernel

theorem prime_16847324489 : Nat.Prime 16847324489 := by
  apply nodeValid_prime [2, 79, 26657159] ⟨16847324489, 3, [(2, 3), (79, 1), (26657159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_26657159
  · decide +kernel

theorem prime_18056084129 : Nat.Prime 18056084129 := by
  apply nodeValid_prime [2, 23, 2239, 10957] ⟨18056084129, 3, [(2, 5), (23, 1), (2239, 1), (10957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_2239
    · exact prime_10957
  · decide +kernel

theorem prime_18705485291 : Nat.Prime 18705485291 := by
  apply nodeValid_prime [2, 5, 461, 4057589] ⟨18705485291, 2, [(2, 1), (5, 1), (461, 1), (4057589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_461
    · exact prime_4057589
  · decide +kernel

theorem prime_37852367873 : Nat.Prime 37852367873 := by
  apply nodeValid_prime [2, 11, 19, 137, 1291] ⟨37852367873, 5, [(2, 10), (11, 1), (19, 1), (137, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19
    · exact prime_137
    · exact prime_1291
  · decide +kernel

theorem prime_50957417081 : Nat.Prime 50957417081 := by
  apply nodeValid_prime [2, 5, 19, 3528907] ⟨50957417081, 3, [(2, 3), (5, 1), (19, 2), (3528907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_3528907
  · decide +kernel

theorem prime_197656221377 : Nat.Prime 197656221377 := by
  apply nodeValid_prime [2, 9907, 311737] ⟨197656221377, 3, [(2, 6), (9907, 1), (311737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9907
    · exact prime_311737
  · decide +kernel

theorem prime_429243293471 : Nat.Prime 429243293471 := by
  apply nodeValid_prime [2, 5, 23, 1866275189] ⟨429243293471, 11, [(2, 1), (5, 1), (23, 1), (1866275189, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_1866275189
  · decide +kernel

theorem prime_643864943387 : Nat.Prime 643864943387 := by
  apply nodeValid_prime [2, 7, 191, 1109, 217121] ⟨643864943387, 2, [(2, 1), (7, 1), (191, 1), (1109, 1), (217121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_191
    · exact prime_1109
    · exact prime_217121
  · decide +kernel

theorem prime_2547870854051 : Nat.Prime 2547870854051 := by
  apply nodeValid_prime [2, 5, 50957417081] ⟨2547870854051, 6, [(2, 1), (5, 2), (50957417081, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_50957417081
  · decide +kernel

theorem prime_5060482621223 : Nat.Prime 5060482621223 := by
  apply nodeValid_prime [2, 7, 43, 53, 158605987] ⟨5060482621223, 5, [(2, 1), (7, 1), (43, 1), (53, 1), (158605987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_53
    · exact prime_158605987
  · decide +kernel

theorem prime_5060482642729 : Nat.Prime 5060482642729 := by
  apply nodeValid_prime [2, 3, 61, 13567, 28309] ⟨5060482642729, 7, [(2, 3), (3, 3), (61, 1), (13567, 1), (28309, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_13567
    · exact prime_28309
  · decide +kernel

theorem prime_5060482643059 : Nat.Prime 5060482643059 := by
  apply nodeValid_prime [2, 3, 53, 15913467431] ⟨5060482643059, 2, [(2, 1), (3, 1), (53, 1), (15913467431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_15913467431
  · decide +kernel

theorem prime_5064392096741 : Nat.Prime 5064392096741 := by
  apply nodeValid_prime [2, 5, 19, 13327347623] ⟨5064392096741, 2, [(2, 2), (5, 1), (19, 1), (13327347623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_13327347623
  · decide +kernel

theorem prime_5064392140933 : Nat.Prime 5064392140933 := by
  apply nodeValid_prime [2, 3, 10651, 39623761] ⟨5064392140933, 5, [(2, 2), (3, 1), (10651, 1), (39623761, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10651
    · exact prime_39623761
  · decide +kernel

theorem prime_5064392140943 : Nat.Prime 5064392140943 := by
  apply nodeValid_prime [2, 73043, 34667197] ⟨5064392140943, 5, [(2, 1), (73043, 1), (34667197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73043
    · exact prime_34667197
  · decide +kernel

theorem prime_5068303522141 : Nat.Prime 5068303522141 := by
  apply nodeValid_prime [2, 3, 5, 137, 616581937] ⟨5068303522141, 2, [(2, 2), (3, 1), (5, 1), (137, 1), (616581937, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
    · exact prime_616581937
  · decide +kernel

theorem prime_5068303522313 : Nat.Prime 5068303522313 := by
  apply nodeValid_prime [2, 251, 2524055539] ⟨5068303522313, 3, [(2, 3), (251, 1), (2524055539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_251
    · exact prime_2524055539
  · decide +kernel

theorem prime_5068303611817 : Nat.Prime 5068303611817 := by
  apply nodeValid_prime [2, 3, 61, 2699, 1282681] ⟨5068303611817, 10, [(2, 3), (3, 1), (61, 1), (2699, 1), (1282681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_2699
    · exact prime_1282681
  · decide +kernel

theorem prime_5072217186697 : Nat.Prime 5072217186697 := by
  apply nodeValid_prime [2, 3, 11, 151, 11261, 11299] ⟨5072217186697, 7, [(2, 3), (3, 1), (11, 1), (151, 1), (11261, 1), (11299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_151
    · exact prime_11261
    · exact prime_11299
  · decide +kernel

theorem prime_5072217292823 : Nat.Prime 5072217292823 := by
  apply nodeValid_prime [2, 97, 1277, 20474119] ⟨5072217292823, 5, [(2, 1), (97, 1), (1277, 1), (20474119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1277
    · exact prime_20474119
  · decide +kernel

theorem prime_5072217294983 : Nat.Prime 5072217294983 := by
  apply nodeValid_prime [2, 67, 37852367873] ⟨5072217294983, 5, [(2, 1), (67, 1), (37852367873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_37852367873
  · decide +kernel

theorem prime_5076132805087 : Nat.Prime 5076132805087 := by
  apply nodeValid_prime [2, 3, 7, 17, 53, 79, 99881] ⟨5076132805087, 7, [(2, 1), (3, 1), (7, 1), (17, 2), (53, 1), (79, 1), (99881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_53
    · exact prime_79
    · exact prime_99881
  · decide +kernel

theorem prime_5076132805369 : Nat.Prime 5076132805369 := by
  apply nodeValid_prime [2, 3, 31, 521, 797, 5477] ⟨5076132805369, 7, [(2, 3), (3, 2), (31, 1), (521, 1), (797, 1), (5477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_521
    · exact prime_797
    · exact prime_5477
  · decide +kernel

theorem prime_5076132814561 : Nat.Prime 5076132814561 := by
  apply nodeValid_prime [2, 3, 5, 23, 2333, 197083] ⟨5076132814561, 11, [(2, 5), (3, 1), (5, 1), (23, 1), (2333, 1), (197083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_2333
    · exact prime_197083
  · decide +kernel

theorem prime_5080050486761 : Nat.Prime 5080050486761 := by
  apply nodeValid_prime [2, 5, 25171, 5045539] ⟨5080050486761, 3, [(2, 3), (5, 1), (25171, 1), (5045539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_25171
    · exact prime_5045539
  · decide +kernel

theorem prime_5080050537173 : Nat.Prime 5080050537173 := by
  apply nodeValid_prime [2, 13, 113, 864542297] ⟨5080050537173, 3, [(2, 2), (13, 1), (113, 1), (864542297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
    · exact prime_864542297
  · decide +kernel

theorem prime_5080050538319 : Nat.Prime 5080050538319 := by
  apply nodeValid_prime [2, 7, 17, 3049250023] ⟨5080050538319, 11, [(2, 1), (7, 2), (17, 1), (3049250023, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_3049250023
  · decide +kernel

theorem prime_5083970211871 : Nat.Prime 5083970211871 := by
  apply nodeValid_prime [2, 3, 5, 11, 967, 2111, 7547] ⟨5083970211871, 6, [(2, 1), (3, 1), (5, 1), (11, 1), (967, 1), (2111, 1), (7547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_967
    · exact prime_2111
    · exact prime_7547
  · decide +kernel

theorem prime_5083970344153 : Nat.Prime 5083970344153 := by
  apply nodeValid_prime [2, 3, 7, 37, 269, 607, 5009] ⟨5083970344153, 5, [(2, 3), (3, 1), (7, 1), (37, 1), (269, 1), (607, 1), (5009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_269
    · exact prime_607
    · exact prime_5009
  · decide +kernel

theorem prime_5083970345429 : Nat.Prime 5083970345429 := by
  apply nodeValid_prime [2, 13, 68891, 1419179] ⟨5083970345429, 2, [(2, 2), (13, 1), (68891, 1), (1419179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_68891
    · exact prime_1419179
  · decide +kernel

theorem prime_5087891989223 : Nat.Prime 5087891989223 := by
  apply nodeValid_prime [2, 7, 109, 3334136297] ⟨5087891989223, 5, [(2, 1), (7, 1), (109, 1), (3334136297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_109
    · exact prime_3334136297
  · decide +kernel

theorem prime_5087891995679 : Nat.Prime 5087891995679 := by
  apply nodeValid_prime [2, 151, 16847324489] ⟨5087891995679, 11, [(2, 1), (151, 1), (16847324489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_151
    · exact prime_16847324489
  · decide +kernel

theorem prime_5087891999153 : Nat.Prime 5087891999153 := by
  apply nodeValid_prime [2, 17, 18705485291] ⟨5087891999153, 5, [(2, 4), (17, 1), (18705485291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_18705485291
  · decide +kernel

theorem prime_5091815722979 : Nat.Prime 5091815722979 := by
  apply nodeValid_prime [2, 79, 2371, 13592021] ⟨5091815722979, 2, [(2, 1), (79, 1), (2371, 1), (13592021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_2371
    · exact prime_13592021
  · decide +kernel

theorem prime_5091815724379 : Nat.Prime 5091815724379 := by
  apply nodeValid_prime [2, 3, 47, 18056084129] ⟨5091815724379, 3, [(2, 1), (3, 1), (47, 1), (18056084129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_18056084129
  · decide +kernel

theorem prime_5091815823631 : Nat.Prime 5091815823631 := by
  apply nodeValid_prime [2, 3, 5, 54917, 3090613] ⟨5091815823631, 6, [(2, 1), (3, 1), (5, 1), (54917, 1), (3090613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_54917
    · exact prime_3090613
  · decide +kernel

theorem prime_5095741708103 : Nat.Prime 5095741708103 := by
  apply nodeValid_prime [2, 2547870854051] ⟨5095741708103, 5, [(2, 1), (2547870854051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2547870854051
  · decide +kernel

theorem prime_5095741760999 : Nat.Prime 5095741760999 := by
  apply nodeValid_prime [2, 7, 127, 2865996491] ⟨5095741760999, 7, [(2, 1), (7, 1), (127, 1), (2865996491, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_127
    · exact prime_2865996491
  · decide +kernel

theorem prime_5095741761377 : Nat.Prime 5095741761377 := by
  apply nodeValid_prime [2, 7, 31, 1699, 61703] ⟨5095741761377, 3, [(2, 5), (7, 2), (31, 1), (1699, 1), (61703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_31
    · exact prime_1699
    · exact prime_61703
  · decide +kernel

theorem prime_5099669650241 : Nat.Prime 5099669650241 := by
  apply nodeValid_prime [2, 5, 11, 53, 97, 281807] ⟨5099669650241, 3, [(2, 6), (5, 1), (11, 1), (53, 1), (97, 1), (281807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_53
    · exact prime_97
    · exact prime_281807
  · decide +kernel

theorem prime_5099669650987 : Nat.Prime 5099669650987 := by
  apply nodeValid_prime [2, 3, 1217, 698393543] ⟨5099669650987, 2, [(2, 1), (3, 1), (1217, 1), (698393543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1217
    · exact prime_698393543
  · decide +kernel

theorem prime_5099669652061 : Nat.Prime 5099669652061 := by
  apply nodeValid_prime [2, 3, 5, 197, 3643, 13159] ⟨5099669652061, 6, [(2, 2), (3, 3), (5, 1), (197, 1), (3643, 1), (13159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_197
    · exact prime_3643
    · exact prime_13159
  · decide +kernel

theorem prime_5103599591093 : Nat.Prime 5103599591093 := by
  apply nodeValid_prime [2, 2221, 574470913] ⟨5103599591093, 2, [(2, 2), (2221, 1), (574470913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2221
    · exact prime_574470913
  · decide +kernel

theorem prime_5103599591837 : Nat.Prime 5103599591837 := by
  apply nodeValid_prime [2, 109, 353, 33160067] ⟨5103599591837, 2, [(2, 2), (109, 1), (353, 1), (33160067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_353
    · exact prime_33160067
  · decide +kernel

theorem prime_5103599640743 : Nat.Prime 5103599640743 := by
  apply nodeValid_prime [2, 23, 79, 97, 139, 104161] ⟨5103599640743, 5, [(2, 1), (23, 1), (79, 1), (97, 1), (139, 1), (104161, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_79
    · exact prime_97
    · exact prime_139
    · exact prime_104161
  · decide +kernel

theorem prime_5107531679807 : Nat.Prime 5107531679807 := by
  apply nodeValid_prime [2, 317, 8056043659] ⟨5107531679807, 5, [(2, 1), (317, 1), (8056043659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_317
    · exact prime_8056043659
  · decide +kernel

theorem prime_5107531738513 : Nat.Prime 5107531738513 := by
  apply nodeValid_prime [2, 3, 7, 15200987317] ⟨5107531738513, 5, [(2, 4), (3, 1), (7, 1), (15200987317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_15200987317
  · decide +kernel

theorem prime_5107531739701 : Nat.Prime 5107531739701 := by
  apply nodeValid_prime [2, 3, 5, 13, 43, 2342797] ⟨5107531739701, 11, [(2, 2), (3, 1), (5, 2), (13, 2), (43, 1), (2342797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_2342797
  · decide +kernel

theorem prime_5111465764981 : Nat.Prime 5111465764981 := by
  apply nodeValid_prime [2, 3, 5, 43, 389, 5093029] ⟨5111465764981, 2, [(2, 2), (3, 1), (5, 1), (43, 1), (389, 1), (5093029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_389
    · exact prime_5093029
  · decide +kernel

theorem prime_5111465765261 : Nat.Prime 5111465765261 := by
  apply nodeValid_prime [2, 5, 17, 9103, 1651513] ⟨5111465765261, 2, [(2, 2), (5, 1), (17, 1), (9103, 1), (1651513, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_9103
    · exact prime_1651513
  · decide +kernel

theorem prime_5111465773481 : Nat.Prime 5111465773481 := by
  apply nodeValid_prime [2, 5, 11, 11616967667] ⟨5111465773481, 3, [(2, 3), (5, 1), (11, 1), (11616967667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_11616967667
  · decide +kernel

theorem prime_5115401904761 : Nat.Prime 5115401904761 := by
  apply nodeValid_prime [2, 5, 7, 2609898931] ⟨5115401904761, 6, [(2, 3), (5, 1), (7, 2), (2609898931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2609898931
  · decide +kernel

theorem prime_5115401905127 : Nat.Prime 5115401905127 := by
  apply nodeValid_prime [2, 659, 3881185057] ⟨5115401905127, 5, [(2, 1), (659, 1), (3881185057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_659
    · exact prime_3881185057
  · decide +kernel

theorem prime_5115401914237 : Nat.Prime 5115401914237 := by
  apply nodeValid_prime [2, 3, 13933, 30595241] ⟨5115401914237, 2, [(2, 2), (3, 1), (13933, 1), (30595241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13933
    · exact prime_30595241
  · decide +kernel

theorem prime_5119340083301 : Nat.Prime 5119340083301 := by
  apply nodeValid_prime [2, 5, 17669, 2897357] ⟨5119340083301, 2, [(2, 2), (5, 2), (17669, 1), (2897357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17669
    · exact prime_2897357
  · decide +kernel

theorem prime_5119340083577 : Nat.Prime 5119340083577 := by
  apply nodeValid_prime [2, 31, 23789, 867733] ⟨5119340083577, 3, [(2, 3), (31, 1), (23789, 1), (867733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_23789
    · exact prime_867733
  · decide +kernel

theorem prime_5119340104391 : Nat.Prime 5119340104391 := by
  apply nodeValid_prime [2, 5, 16879, 30329641] ⟨5119340104391, 13, [(2, 1), (5, 1), (16879, 1), (30329641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_16879
    · exact prime_30329641
  · decide +kernel

theorem prime_5123280339803 : Nat.Prime 5123280339803 := by
  apply nodeValid_prime [2, 43, 181, 2083, 158009] ⟨5123280339803, 2, [(2, 1), (43, 1), (181, 1), (2083, 1), (158009, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_181
    · exact prime_2083
    · exact prime_158009
  · decide +kernel

theorem prime_5123280372053 : Nat.Prime 5123280372053 := by
  apply nodeValid_prime [2, 23, 43, 541, 2393837] ⟨5123280372053, 2, [(2, 2), (23, 1), (43, 1), (541, 1), (2393837, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_43
    · exact prime_541
    · exact prime_2393837
  · decide +kernel

theorem prime_5123280372403 : Nat.Prime 5123280372403 := by
  apply nodeValid_prime [2, 3, 877, 1279, 761249] ⟨5123280372403, 2, [(2, 1), (3, 1), (877, 1), (1279, 1), (761249, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_877
    · exact prime_1279
    · exact prime_761249
  · decide +kernel

theorem prime_5127222519857 : Nat.Prime 5127222519857 := by
  apply nodeValid_prime [2, 47, 193, 35327021] ⟨5127222519857, 3, [(2, 4), (47, 1), (193, 1), (35327021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_193
    · exact prime_35327021
  · decide +kernel

theorem prime_5127222520339 : Nat.Prime 5127222520339 := by
  apply nodeValid_prime [2, 3, 1297, 658856659] ⟨5127222520339, 3, [(2, 1), (3, 1), (1297, 1), (658856659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1297
    · exact prime_658856659
  · decide +kernel

theorem prime_5127222632879 : Nat.Prime 5127222632879 := by
  apply nodeValid_prime [2, 41, 2381, 26260859] ⟨5127222632879, 7, [(2, 1), (41, 1), (2381, 1), (26260859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_2381
    · exact prime_26260859
  · decide +kernel

theorem prime_5131166969549 : Nat.Prime 5131166969549 := by
  apply nodeValid_prime [2, 127, 131, 787, 97973] ⟨5131166969549, 2, [(2, 2), (127, 1), (131, 1), (787, 1), (97973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_131
    · exact prime_787
    · exact prime_97973
  · decide +kernel

theorem prime_5131166970977 : Nat.Prime 5131166970977 := by
  apply nodeValid_prime [2, 101, 1587613543] ⟨5131166970977, 3, [(2, 5), (101, 1), (1587613543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_101
    · exact prime_1587613543
  · decide +kernel

theorem prime_5131166980391 : Nat.Prime 5131166980391 := by
  apply nodeValid_prime [2, 5, 11, 24023, 1941763] ⟨5131166980391, 14, [(2, 1), (5, 1), (11, 1), (24023, 1), (1941763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_24023
    · exact prime_1941763
  · decide +kernel

theorem prime_5135113385761 : Nat.Prime 5135113385761 := by
  apply nodeValid_prime [2, 3, 5, 17, 629303111] ⟨5135113385761, 13, [(2, 5), (3, 1), (5, 1), (17, 1), (629303111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_629303111
  · decide +kernel

theorem prime_5135113413257 : Nat.Prime 5135113413257 := by
  apply nodeValid_prime [2, 41, 19763, 792179] ⟨5135113413257, 3, [(2, 3), (41, 1), (19763, 1), (792179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_19763
    · exact prime_792179
  · decide +kernel

theorem prime_5135113414019 : Nat.Prime 5135113414019 := by
  apply nodeValid_prime [2, 7, 547, 5333, 125737] ⟨5135113414019, 6, [(2, 1), (7, 1), (547, 1), (5333, 1), (125737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_547
    · exact prime_5333
    · exact prime_125737
  · decide +kernel

theorem prime_5139061755643 : Nat.Prime 5139061755643 := by
  apply nodeValid_prime [2, 3, 1193, 5881, 40693] ⟨5139061755643, 2, [(2, 1), (3, 2), (1193, 1), (5881, 1), (40693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1193
    · exact prime_5881
    · exact prime_40693
  · decide +kernel

theorem prime_5139061755803 : Nat.Prime 5139061755803 := by
  apply nodeValid_prime [2, 13, 197656221377] ⟨5139061755803, 2, [(2, 1), (13, 1), (197656221377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_197656221377
  · decide +kernel

theorem prime_5139061845361 : Nat.Prime 5139061845361 := by
  apply nodeValid_prime [2, 3, 5, 31, 191, 3616409] ⟨5139061845361, 14, [(2, 4), (3, 1), (5, 1), (31, 1), (191, 1), (3616409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_31
    · exact prime_191
    · exact prime_3616409
  · decide +kernel

theorem prime_5143012355213 : Nat.Prime 5143012355213 := by
  apply nodeValid_prime [2, 29, 67, 73, 9064877] ⟨5143012355213, 2, [(2, 2), (29, 1), (67, 1), (73, 1), (9064877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_67
    · exact prime_73
    · exact prime_9064877
  · decide +kernel

theorem prime_5143012355321 : Nat.Prime 5143012355321 := by
  apply nodeValid_prime [2, 5, 7, 23, 798604403] ⟨5143012355321, 3, [(2, 3), (5, 1), (7, 1), (23, 1), (798604403, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_23
    · exact prime_798604403
  · decide +kernel

theorem prime_5143012356007 : Nat.Prime 5143012356007 := by
  apply nodeValid_prime [2, 3, 7, 353, 115630477] ⟨5143012356007, 3, [(2, 1), (3, 2), (7, 1), (353, 1), (115630477, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_353
    · exact prime_115630477
  · decide +kernel

theorem prime_5146964909633 : Nat.Prime 5146964909633 := by
  apply nodeValid_prime [2, 7, 13, 29, 1483, 20549] ⟨5146964909633, 3, [(2, 6), (7, 1), (13, 1), (29, 1), (1483, 1), (20549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_29
    · exact prime_1483
    · exact prime_20549
  · decide +kernel

theorem prime_5146964937787 : Nat.Prime 5146964937787 := by
  apply nodeValid_prime [2, 3, 7, 29063, 4216591] ⟨5146964937787, 2, [(2, 1), (3, 1), (7, 1), (29063, 1), (4216591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_29063
    · exact prime_4216591
  · decide +kernel

theorem prime_5146964941543 : Nat.Prime 5146964941543 := by
  apply nodeValid_prime [2, 3, 163, 787, 6687097] ⟨5146964941543, 5, [(2, 1), (3, 1), (163, 1), (787, 1), (6687097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_163
    · exact prime_787
    · exact prime_6687097
  · decide +kernel

theorem prime_5150919521653 : Nat.Prime 5150919521653 := by
  apply nodeValid_prime [2, 3, 429243293471] ⟨5150919521653, 2, [(2, 2), (3, 1), (429243293471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_429243293471
  · decide +kernel

theorem prime_5150919547097 : Nat.Prime 5150919547097 := by
  apply nodeValid_prime [2, 643864943387] ⟨5150919547097, 3, [(2, 3), (643864943387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_643864943387
  · decide +kernel

theorem prime_5150919548107 : Nat.Prime 5150919548107 := by
  apply nodeValid_prime [2, 3, 769, 1087, 114113] ⟨5150919548107, 2, [(2, 1), (3, 3), (769, 1), (1087, 1), (114113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_769
    · exact prime_1087
    · exact prime_114113
  · decide +kernel

theorem prime_5154876193177 : Nat.Prime 5154876193177 := by
  apply nodeValid_prime [2, 3, 110927, 215143] ⟨5154876193177, 5, [(2, 3), (3, 3), (110927, 1), (215143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_110927
    · exact prime_215143
  · decide +kernel

theorem prime_5154876215891 : Nat.Prime 5154876215891 := by
  apply nodeValid_prime [2, 5, 43, 383, 31300481] ⟨5154876215891, 2, [(2, 1), (5, 1), (43, 1), (383, 1), (31300481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_383
    · exact prime_31300481
  · decide +kernel

theorem prime_5154876215893 : Nat.Prime 5154876215893 := by
  apply nodeValid_prime [2, 3, 13, 857, 12852617] ⟨5154876215893, 2, [(2, 2), (3, 2), (13, 1), (857, 1), (12852617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_857
    · exact prime_12852617
  · decide +kernel

end Sude.Lucas.Generated
