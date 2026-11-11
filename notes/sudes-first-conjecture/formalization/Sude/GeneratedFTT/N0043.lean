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
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0019
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0023
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0029
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0034
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0041
import Sude.GeneratedFTT.N0042

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2969 : Nat.Prime 2969 := by
  apply nodeValid_prime [2, 7, 53] ⟨2969, 3, [(2, 3), (7, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_53
  · decide +kernel

theorem prime_3833 : Nat.Prime 3833 := by
  apply nodeValid_prime [2, 479] ⟨3833, 3, [(2, 3), (479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_479
  · decide +kernel

theorem prime_5927 : Nat.Prime 5927 := by
  apply nodeValid_prime [2, 2963] ⟨5927, 5, [(2, 1), (2963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2963
  · decide +kernel

theorem prime_7103 : Nat.Prime 7103 := by
  apply nodeValid_prime [2, 53, 67] ⟨7103, 5, [(2, 1), (53, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_67
  · decide +kernel

theorem prime_9049 : Nat.Prime 9049 := by
  apply nodeValid_prime [2, 3, 13, 29] ⟨9049, 7, [(2, 3), (3, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_9817 : Nat.Prime 9817 := by
  apply nodeValid_prime [2, 3, 409] ⟨9817, 5, [(2, 3), (3, 1), (409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_409
  · decide +kernel

theorem prime_11171 : Nat.Prime 11171 := by
  apply nodeValid_prime [2, 5, 1117] ⟨11171, 2, [(2, 1), (5, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1117
  · decide +kernel

theorem prime_12433 : Nat.Prime 12433 := by
  apply nodeValid_prime [2, 3, 7, 37] ⟨12433, 13, [(2, 4), (3, 1), (7, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
  · decide +kernel

theorem prime_17891 : Nat.Prime 17891 := by
  apply nodeValid_prime [2, 5, 1789] ⟨17891, 2, [(2, 1), (5, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1789
  · decide +kernel

theorem prime_19991 : Nat.Prime 19991 := by
  apply nodeValid_prime [2, 5, 1999] ⟨19991, 11, [(2, 1), (5, 1), (1999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1999
  · decide +kernel

theorem prime_21187 : Nat.Prime 21187 := by
  apply nodeValid_prime [2, 3, 11, 107] ⟨21187, 2, [(2, 1), (3, 2), (11, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_107
  · decide +kernel

theorem prime_24499 : Nat.Prime 24499 := by
  apply nodeValid_prime [2, 3, 1361] ⟨24499, 2, [(2, 1), (3, 2), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1361
  · decide +kernel

theorem prime_33179 : Nat.Prime 33179 := by
  apply nodeValid_prime [2, 53, 313] ⟨33179, 2, [(2, 1), (53, 1), (313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_313
  · decide +kernel

theorem prime_36341 : Nat.Prime 36341 := by
  apply nodeValid_prime [2, 5, 23, 79] ⟨36341, 2, [(2, 2), (5, 1), (23, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_79
  · decide +kernel

theorem prime_39983 : Nat.Prime 39983 := by
  apply nodeValid_prime [2, 19991] ⟨39983, 5, [(2, 1), (19991, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19991
  · decide +kernel

theorem prime_40763 : Nat.Prime 40763 := by
  apply nodeValid_prime [2, 89, 229] ⟨40763, 2, [(2, 1), (89, 1), (229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_89
    · exact prime_229
  · decide +kernel

theorem prime_42683 : Nat.Prime 42683 := by
  apply nodeValid_prime [2, 21341] ⟨42683, 2, [(2, 1), (21341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_21341
  · decide +kernel

theorem prime_42701 : Nat.Prime 42701 := by
  apply nodeValid_prime [2, 5, 7, 61] ⟨42701, 3, [(2, 2), (5, 2), (7, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_61
  · decide +kernel

theorem prime_45659 : Nat.Prime 45659 := by
  apply nodeValid_prime [2, 37, 617] ⟨45659, 2, [(2, 1), (37, 1), (617, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_617
  · decide +kernel

theorem prime_54673 : Nat.Prime 54673 := by
  apply nodeValid_prime [2, 3, 17, 67] ⟨54673, 5, [(2, 4), (3, 1), (17, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_67
  · decide +kernel

theorem prime_56123 : Nat.Prime 56123 := by
  apply nodeValid_prime [2, 11, 2551] ⟨56123, 2, [(2, 1), (11, 1), (2551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_2551
  · decide +kernel

theorem prime_56393 : Nat.Prime 56393 := by
  apply nodeValid_prime [2, 7, 19, 53] ⟨56393, 3, [(2, 3), (7, 1), (19, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_53
  · decide +kernel

theorem prime_65993 : Nat.Prime 65993 := by
  apply nodeValid_prime [2, 73, 113] ⟨65993, 3, [(2, 3), (73, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_113
  · decide +kernel

theorem prime_66359 : Nat.Prime 66359 := by
  apply nodeValid_prime [2, 33179] ⟨66359, 13, [(2, 1), (33179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_33179
  · decide +kernel

theorem prime_79967 : Nat.Prime 79967 := by
  apply nodeValid_prime [2, 39983] ⟨79967, 5, [(2, 1), (39983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39983
  · decide +kernel

theorem prime_101839 : Nat.Prime 101839 := by
  apply nodeValid_prime [2, 3, 11, 1543] ⟨101839, 15, [(2, 1), (3, 1), (11, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_1543
  · decide +kernel

theorem prime_105863 : Nat.Prime 105863 := by
  apply nodeValid_prime [2, 41, 1291] ⟨105863, 5, [(2, 1), (41, 1), (1291, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_1291
  · decide +kernel

theorem prime_112247 : Nat.Prime 112247 := by
  apply nodeValid_prime [2, 56123] ⟨112247, 5, [(2, 1), (56123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56123
  · decide +kernel

theorem prime_112787 : Nat.Prime 112787 := by
  apply nodeValid_prime [2, 56393] ⟨112787, 2, [(2, 1), (56393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_56393
  · decide +kernel

theorem prime_124297 : Nat.Prime 124297 := by
  apply nodeValid_prime [2, 3, 5179] ⟨124297, 5, [(2, 3), (3, 1), (5179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5179
  · decide +kernel

theorem prime_126851 : Nat.Prime 126851 := by
  apply nodeValid_prime [2, 5, 43, 59] ⟨126851, 2, [(2, 1), (5, 2), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_155269 : Nat.Prime 155269 := by
  apply nodeValid_prime [2, 3, 19, 227] ⟨155269, 6, [(2, 2), (3, 2), (19, 1), (227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_227
  · decide +kernel

theorem prime_163927 : Nat.Prime 163927 := by
  apply nodeValid_prime [2, 3, 7, 1301] ⟨163927, 3, [(2, 1), (3, 2), (7, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1301
  · decide +kernel

theorem prime_211727 : Nat.Prime 211727 := by
  apply nodeValid_prime [2, 105863] ⟨211727, 5, [(2, 1), (105863, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_105863
  · decide +kernel

theorem prime_224473 : Nat.Prime 224473 := by
  apply nodeValid_prime [2, 3, 47, 199] ⟨224473, 10, [(2, 3), (3, 1), (47, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_199
  · decide +kernel

theorem prime_231809 : Nat.Prime 231809 := by
  apply nodeValid_prime [2, 1811] ⟨231809, 3, [(2, 7), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1811
  · decide +kernel

theorem prime_234181 : Nat.Prime 234181 := by
  apply nodeValid_prime [2, 3, 5, 1301] ⟨234181, 2, [(2, 2), (3, 2), (5, 1), (1301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1301
  · decide +kernel

theorem prime_266977 : Nat.Prime 266977 := by
  apply nodeValid_prime [2, 3, 103] ⟨266977, 5, [(2, 5), (3, 4), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_267301 : Nat.Prime 267301 := by
  apply nodeValid_prime [2, 3, 5, 11] ⟨267301, 2, [(2, 2), (3, 5), (5, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · decide +kernel

theorem prime_293989 : Nat.Prime 293989 := by
  apply nodeValid_prime [2, 3, 24499] ⟨293989, 2, [(2, 2), (3, 1), (24499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_24499
  · decide +kernel

theorem prime_311747 : Nat.Prime 311747 := by
  apply nodeValid_prime [2, 17, 53, 173] ⟨311747, 2, [(2, 1), (17, 1), (53, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_53
    · exact prime_173
  · decide +kernel

theorem prime_316223 : Nat.Prime 316223 := by
  apply nodeValid_prime [2, 43, 3677] ⟨316223, 5, [(2, 1), (43, 1), (3677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_3677
  · decide +kernel

theorem prime_335021 : Nat.Prime 335021 := by
  apply nodeValid_prime [2, 5, 7, 2393] ⟨335021, 2, [(2, 2), (5, 1), (7, 1), (2393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2393
  · decide +kernel

theorem prime_336961 : Nat.Prime 336961 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨336961, 29, [(2, 6), (3, 4), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_376127 : Nat.Prime 376127 := by
  apply nodeValid_prime [2, 61, 3083] ⟨376127, 5, [(2, 1), (61, 1), (3083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_3083
  · decide +kernel

theorem prime_432631 : Nat.Prime 432631 := by
  apply nodeValid_prime [2, 3, 5, 11, 19, 23] ⟨432631, 19, [(2, 1), (3, 2), (5, 1), (11, 1), (19, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_19
    · exact prime_23
  · decide +kernel

theorem prime_434353 : Nat.Prime 434353 := by
  apply nodeValid_prime [2, 3, 9049] ⟨434353, 5, [(2, 4), (3, 1), (9049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9049
  · decide +kernel

theorem prime_492911 : Nat.Prime 492911 := by
  apply nodeValid_prime [2, 5, 11, 4481] ⟨492911, 33, [(2, 1), (5, 1), (11, 1), (4481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_4481
  · decide +kernel

theorem prime_505157 : Nat.Prime 505157 := by
  apply nodeValid_prime [2, 47, 2687] ⟨505157, 2, [(2, 2), (47, 1), (2687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_2687
  · decide +kernel

theorem prime_508471 : Nat.Prime 508471 := by
  apply nodeValid_prime [2, 3, 5, 17, 997] ⟨508471, 15, [(2, 1), (3, 1), (5, 1), (17, 1), (997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_997
  · decide +kernel

theorem prime_568963 : Nat.Prime 568963 := by
  apply nodeValid_prime [2, 3, 73, 433] ⟨568963, 2, [(2, 1), (3, 2), (73, 1), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_433
  · decide +kernel

theorem prime_598379 : Nat.Prime 598379 := by
  apply nodeValid_prime [2, 11, 59, 461] ⟨598379, 2, [(2, 1), (11, 1), (59, 1), (461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_461
  · decide +kernel

theorem prime_626341 : Nat.Prime 626341 := by
  apply nodeValid_prime [2, 3, 5, 11, 13, 73] ⟨626341, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_815261 : Nat.Prime 815261 := by
  apply nodeValid_prime [2, 5, 40763] ⟨815261, 2, [(2, 2), (5, 1), (40763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40763
  · decide +kernel

theorem prime_880331 : Nat.Prime 880331 := by
  apply nodeValid_prime [2, 5, 11, 53, 151] ⟨880331, 7, [(2, 1), (5, 1), (11, 1), (53, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_53
    · exact prime_151
  · decide +kernel

theorem prime_1076707 : Nat.Prime 1076707 := by
  apply nodeValid_prime [2, 3, 127, 157] ⟨1076707, 3, [(2, 1), (3, 3), (127, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
    · exact prime_157
  · decide +kernel

theorem prime_1145191 : Nat.Prime 1145191 := by
  apply nodeValid_prime [2, 3, 5, 59, 647] ⟨1145191, 3, [(2, 1), (3, 1), (5, 1), (59, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_647
  · decide +kernel

theorem prime_1194463 : Nat.Prime 1194463 := by
  apply nodeValid_prime [2, 3, 66359] ⟨1194463, 5, [(2, 1), (3, 2), (66359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66359
  · decide +kernel

theorem prime_1210169 : Nat.Prime 1210169 := by
  apply nodeValid_prime [2, 23, 6577] ⟨1210169, 6, [(2, 3), (23, 1), (6577, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_6577
  · decide +kernel

theorem prime_2100713 : Nat.Prime 2100713 := by
  apply nodeValid_prime [2, 37, 47, 151] ⟨2100713, 3, [(2, 3), (37, 1), (47, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_47
    · exact prime_151
  · decide +kernel

theorem prime_2135051 : Nat.Prime 2135051 := by
  apply nodeValid_prime [2, 5, 42701] ⟨2135051, 2, [(2, 1), (5, 2), (42701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_42701
  · decide +kernel

theorem prime_2275853 : Nat.Prime 2275853 := by
  apply nodeValid_prime [2, 568963] ⟨2275853, 2, [(2, 2), (568963, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_568963
  · decide +kernel

theorem prime_2399011 : Nat.Prime 2399011 := by
  apply nodeValid_prime [2, 3, 5, 79967] ⟨2399011, 3, [(2, 1), (3, 1), (5, 1), (79967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_79967
  · decide +kernel

theorem prime_2420339 : Nat.Prime 2420339 := by
  apply nodeValid_prime [2, 1210169] ⟨2420339, 2, [(2, 1), (1210169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1210169
  · decide +kernel

theorem prime_2528233 : Nat.Prime 2528233 := by
  apply nodeValid_prime [2, 3, 7, 101, 149] ⟨2528233, 5, [(2, 3), (3, 1), (7, 1), (101, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_101
    · exact prime_149
  · decide +kernel

theorem prime_2810173 : Nat.Prime 2810173 := by
  apply nodeValid_prime [2, 3, 234181] ⟨2810173, 2, [(2, 2), (3, 1), (234181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_234181
  · decide +kernel

theorem prime_2936803 : Nat.Prime 2936803 := by
  apply nodeValid_prime [2, 3, 11, 44497] ⟨2936803, 3, [(2, 1), (3, 1), (11, 1), (44497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_44497
  · decide +kernel

theorem prime_3644983 : Nat.Prime 3644983 := by
  apply nodeValid_prime [2, 3, 11, 41, 449] ⟨3644983, 3, [(2, 1), (3, 2), (11, 1), (41, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_41
    · exact prime_449
  · decide +kernel

theorem prime_3941969 : Nat.Prime 3941969 := by
  apply nodeValid_prime [2, 19, 12967] ⟨3941969, 3, [(2, 4), (19, 1), (12967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_12967
  · decide +kernel

theorem prime_4159279 : Nat.Prime 4159279 := by
  apply nodeValid_prime [2, 3, 269, 859] ⟨4159279, 11, [(2, 1), (3, 2), (269, 1), (859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
    · exact prime_859
  · decide +kernel

theorem prime_4270103 : Nat.Prime 4270103 := by
  apply nodeValid_prime [2, 2135051] ⟨4270103, 5, [(2, 1), (2135051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2135051
  · decide +kernel

theorem prime_6483839 : Nat.Prime 6483839 := by
  apply nodeValid_prime [2, 23, 47, 2999] ⟨6483839, 13, [(2, 1), (23, 1), (47, 1), (2999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_47
    · exact prime_2999
  · decide +kernel

theorem prime_7390231 : Nat.Prime 7390231 := by
  apply nodeValid_prime [2, 3, 5, 181, 1361] ⟨7390231, 3, [(2, 1), (3, 1), (5, 1), (181, 1), (1361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
    · exact prime_1361
  · decide +kernel

theorem prime_7399283 : Nat.Prime 7399283 := by
  apply nodeValid_prime [2, 11, 89, 3779] ⟨7399283, 2, [(2, 1), (11, 1), (89, 1), (3779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
    · exact prime_3779
  · decide +kernel

theorem prime_9077219 : Nat.Prime 9077219 := by
  apply nodeValid_prime [2, 17, 266977] ⟨9077219, 6, [(2, 1), (17, 1), (266977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_266977
  · decide +kernel

theorem prime_9344527 : Nat.Prime 9344527 := by
  apply nodeValid_prime [2, 3, 17, 317] ⟨9344527, 6, [(2, 1), (3, 1), (17, 3), (317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_317
  · decide +kernel

theorem prime_9779303 : Nat.Prime 9779303 := by
  apply nodeValid_prime [2, 13, 376127] ⟨9779303, 5, [(2, 1), (13, 1), (376127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_376127
  · decide +kernel

theorem prime_12967679 : Nat.Prime 12967679 := by
  apply nodeValid_prime [2, 6483839] ⟨12967679, 7, [(2, 1), (6483839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6483839
  · decide +kernel

theorem prime_19111409 : Nat.Prime 19111409 := by
  apply nodeValid_prime [2, 1194463] ⟨19111409, 3, [(2, 4), (1194463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1194463
  · decide +kernel

theorem prime_23515691 : Nat.Prime 23515691 := by
  apply nodeValid_prime [2, 5, 11, 313, 683] ⟨23515691, 6, [(2, 1), (5, 1), (11, 1), (313, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_313
    · exact prime_683
  · decide +kernel

theorem prime_30381803 : Nat.Prime 30381803 := by
  apply nodeValid_prime [2, 11, 233, 5927] ⟨30381803, 2, [(2, 1), (11, 1), (233, 1), (5927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_233
    · exact prime_5927
  · decide +kernel

theorem prime_32350667 : Nat.Prime 32350667 := by
  apply nodeValid_prime [2, 1301, 12433] ⟨32350667, 2, [(2, 1), (1301, 1), (12433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1301
    · exact prime_12433
  · decide +kernel

theorem prime_37378109 : Nat.Prime 37378109 := by
  apply nodeValid_prime [2, 9344527] ⟨37378109, 2, [(2, 2), (9344527, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9344527
  · decide +kernel

theorem prime_45792493 : Nat.Prime 45792493 := by
  apply nodeValid_prime [2, 3, 17, 224473] ⟨45792493, 5, [(2, 2), (3, 1), (17, 1), (224473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_224473
  · decide +kernel

theorem prime_57006889 : Nat.Prime 57006889 := by
  apply nodeValid_prime [2, 3, 1451, 1637] ⟨57006889, 41, [(2, 3), (3, 1), (1451, 1), (1637, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1451
    · exact prime_1637
  · decide +kernel

theorem prime_72804313 : Nat.Prime 72804313 := by
  apply nodeValid_prime [2, 3, 7, 179, 269] ⟨72804313, 5, [(2, 3), (3, 3), (7, 1), (179, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_179
    · exact prime_269
  · decide +kernel

theorem prime_105941347 : Nat.Prime 105941347 := by
  apply nodeValid_prime [2, 3, 7, 269, 9377] ⟨105941347, 2, [(2, 1), (3, 1), (7, 1), (269, 1), (9377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_269
    · exact prime_9377
  · decide +kernel

theorem prime_109456957 : Nat.Prime 109456957 := by
  apply nodeValid_prime [2, 3, 7, 434353] ⟨109456957, 2, [(2, 2), (3, 2), (7, 1), (434353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_434353
  · decide +kernel

theorem prime_118222591 : Nat.Prime 118222591 := by
  apply nodeValid_prime [2, 3, 5, 17, 231809] ⟨118222591, 6, [(2, 1), (3, 1), (5, 1), (17, 1), (231809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_231809
  · decide +kernel

theorem prime_163389943 : Nat.Prime 163389943 := by
  apply nodeValid_prime [2, 3, 9077219] ⟨163389943, 5, [(2, 1), (3, 2), (9077219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9077219
  · decide +kernel

theorem prime_176459893 : Nat.Prime 176459893 := by
  apply nodeValid_prime [2, 3, 7, 2100713] ⟨176459893, 5, [(2, 2), (3, 1), (7, 1), (2100713, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_2100713
  · decide +kernel

theorem prime_246613007 : Nat.Prime 246613007 := by
  apply nodeValid_prime [2, 4409, 27967] ⟨246613007, 5, [(2, 1), (4409, 1), (27967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4409
    · exact prime_27967
  · decide +kernel

theorem prime_285718721 : Nat.Prime 285718721 := by
  apply nodeValid_prime [2, 5, 7, 229, 557] ⟨285718721, 3, [(2, 6), (5, 1), (7, 1), (229, 1), (557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_229
    · exact prime_557
  · decide +kernel

theorem prime_499456231 : Nat.Prime 499456231 := by
  apply nodeValid_prime [2, 3, 5, 7, 13, 19, 9629] ⟨499456231, 6, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (19, 1), (9629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_19
    · exact prime_9629
  · decide +kernel

theorem prime_557180213 : Nat.Prime 557180213 := by
  apply nodeValid_prime [2, 3833, 36341] ⟨557180213, 2, [(2, 2), (3833, 1), (36341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3833
    · exact prime_36341
  · decide +kernel

theorem prime_645750827 : Nat.Prime 645750827 := by
  apply nodeValid_prime [2, 7, 4129, 11171] ⟨645750827, 2, [(2, 1), (7, 1), (4129, 1), (11171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_4129
    · exact prime_11171
  · decide +kernel

theorem prime_775542983 : Nat.Prime 775542983 := by
  apply nodeValid_prime [2, 1319, 293989] ⟨775542983, 5, [(2, 1), (1319, 1), (293989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1319
    · exact prime_293989
  · decide +kernel

theorem prime_899695877 : Nat.Prime 899695877 := by
  apply nodeValid_prime [2, 23, 9779303] ⟨899695877, 3, [(2, 2), (23, 1), (9779303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_9779303
  · decide +kernel

theorem prime_1033758353 : Nat.Prime 1033758353 := by
  apply nodeValid_prime [2, 11, 59, 113, 881] ⟨1033758353, 3, [(2, 4), (11, 1), (59, 1), (113, 1), (881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_59
    · exact prime_113
    · exact prime_881
  · decide +kernel

theorem prime_1274477681 : Nat.Prime 1274477681 := by
  apply nodeValid_prime [2, 5, 7, 2275853] ⟨1274477681, 3, [(2, 4), (5, 1), (7, 1), (2275853, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_2275853
  · decide +kernel

theorem prime_1406057251 : Nat.Prime 1406057251 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 499] ⟨1406057251, 3, [(2, 1), (3, 1), (5, 3), (13, 1), (17, 2), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_499
  · decide +kernel

theorem prime_1637920073 : Nat.Prime 1637920073 := by
  apply nodeValid_prime [2, 967, 211727] ⟨1637920073, 3, [(2, 3), (967, 1), (211727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_967
    · exact prime_211727
  · decide +kernel

theorem prime_1972904057 : Nat.Prime 1972904057 := by
  apply nodeValid_prime [2, 246613007] ⟨1972904057, 3, [(2, 3), (246613007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_246613007
  · decide +kernel

theorem prime_3290735449 : Nat.Prime 3290735449 := by
  apply nodeValid_prime [2, 3, 7, 11, 13, 45659] ⟨3290735449, 31, [(2, 3), (3, 2), (7, 1), (11, 1), (13, 1), (45659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_45659
  · decide +kernel

theorem prime_4765138253 : Nat.Prime 4765138253 := by
  apply nodeValid_prime [2, 7, 23, 7399283] ⟨4765138253, 2, [(2, 2), (7, 1), (23, 1), (7399283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_23
    · exact prime_7399283
  · decide +kernel

theorem prime_5779763177 : Nat.Prime 5779763177 := by
  apply nodeValid_prime [2, 11, 61, 1076707] ⟨5779763177, 3, [(2, 3), (11, 1), (61, 1), (1076707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_61
    · exact prime_1076707
  · decide +kernel

theorem prime_8313436927 : Nat.Prime 8313436927 := by
  apply nodeValid_prime [2, 3, 937, 492911] ⟨8313436927, 3, [(2, 1), (3, 2), (937, 1), (492911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_937
    · exact prime_492911
  · decide +kernel

theorem prime_12353516473 : Nat.Prime 12353516473 := by
  apply nodeValid_prime [2, 3, 11, 47, 233, 4273] ⟨12353516473, 10, [(2, 3), (3, 1), (11, 1), (47, 1), (233, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_233
    · exact prime_4273
  · decide +kernel

theorem prime_15987265633 : Nat.Prime 15987265633 := by
  apply nodeValid_prime [2, 3, 13, 4270103] ⟨15987265633, 5, [(2, 5), (3, 2), (13, 1), (4270103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_4270103
  · decide +kernel

theorem prime_21092548931 : Nat.Prime 21092548931 := by
  apply nodeValid_prime [2, 5, 37, 57006889] ⟨21092548931, 6, [(2, 1), (5, 1), (37, 1), (57006889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_37
    · exact prime_57006889
  · decide +kernel

theorem prime_26365686169 : Nat.Prime 26365686169 := by
  apply nodeValid_prime [2, 3, 29, 67, 137, 4127] ⟨26365686169, 17, [(2, 3), (3, 1), (29, 1), (67, 1), (137, 1), (4127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_67
    · exact prime_137
    · exact prime_4127
  · decide +kernel

theorem prime_35154247591 : Nat.Prime 35154247591 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 107, 15803] ⟨35154247591, 3, [(2, 1), (3, 3), (5, 1), (7, 1), (11, 1), (107, 1), (15803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_107
    · exact prime_15803
  · decide +kernel

theorem prime_39310081753 : Nat.Prime 39310081753 := by
  apply nodeValid_prime [2, 3, 1637920073] ⟨39310081753, 7, [(2, 3), (3, 1), (1637920073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1637920073
  · decide +kernel

theorem prime_51702865549 : Nat.Prime 51702865549 := by
  apply nodeValid_prime [2, 3, 23, 433, 432631] ⟨51702865549, 6, [(2, 2), (3, 1), (23, 1), (433, 1), (432631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_433
    · exact prime_432631
  · decide +kernel

theorem prime_63373268029 : Nat.Prime 63373268029 := by
  apply nodeValid_prime [2, 3, 7, 857, 880331] ⟨63373268029, 2, [(2, 2), (3, 1), (7, 1), (857, 1), (880331, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_857
    · exact prime_880331
  · decide +kernel

theorem prime_105462744677 : Nat.Prime 105462744677 := by
  apply nodeValid_prime [2, 26365686169] ⟨105462744677, 2, [(2, 2), (26365686169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_26365686169
  · decide +kernel

theorem prime_159872663059 : Nat.Prime 159872663059 := by
  apply nodeValid_prime [2, 3, 151, 176459893] ⟨159872663059, 2, [(2, 1), (3, 1), (151, 1), (176459893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_176459893
  · decide +kernel

theorem prime_309745936673 : Nat.Prime 309745936673 := by
  apply nodeValid_prime [2, 17, 29, 389, 2969] ⟨309745936673, 3, [(2, 5), (17, 2), (29, 1), (389, 1), (2969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_389
    · exact prime_2969
  · decide +kernel

theorem prime_317344946459 : Nat.Prime 317344946459 := by
  apply nodeValid_prime [2, 307, 12109, 42683] ⟨317344946459, 2, [(2, 1), (307, 1), (12109, 1), (42683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_307
    · exact prime_12109
    · exact prime_42683
  · decide +kernel

theorem prime_319264256981 : Nat.Prime 319264256981 := by
  apply nodeValid_prime [2, 5, 1231, 12967679] ⟨319264256981, 2, [(2, 2), (5, 1), (1231, 1), (12967679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1231
    · exact prime_12967679
  · decide +kernel

theorem prime_619491812509 : Nat.Prime 619491812509 := by
  apply nodeValid_prime [2, 3, 797, 2399011] ⟨619491812509, 2, [(2, 2), (3, 4), (797, 1), (2399011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_797
    · exact prime_2399011
  · decide +kernel

theorem prime_619491873347 : Nat.Prime 619491873347 := by
  apply nodeValid_prime [2, 309745936673] ⟨619491873347, 2, [(2, 1), (309745936673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_309745936673
  · decide +kernel

theorem prime_619491873899 : Nat.Prime 619491873899 := by
  apply nodeValid_prime [2, 157, 1972904057] ⟨619491873899, 2, [(2, 1), (157, 1), (1972904057, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_157
    · exact prime_1972904057
  · decide +kernel

theorem prime_620434384849 : Nat.Prime 620434384849 := by
  apply nodeValid_prime [2, 3, 1093, 3941969] ⟨620434384849, 23, [(2, 4), (3, 2), (1093, 1), (3941969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1093
    · exact prime_3941969
  · decide +kernel

theorem prime_620434386401 : Nat.Prime 620434386401 := by
  apply nodeValid_prime [2, 5, 775542983] ⟨620434386401, 3, [(2, 5), (5, 2), (775542983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_775542983
  · decide +kernel

theorem prime_620434386589 : Nat.Prime 620434386589 := by
  apply nodeValid_prime [2, 3, 51702865549] ⟨620434386589, 6, [(2, 2), (3, 1), (51702865549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_51702865549
  · decide +kernel

theorem prime_621377880821 : Nat.Prime 621377880821 := by
  apply nodeValid_prime [2, 5, 877, 4229, 8377] ⟨621377880821, 2, [(2, 2), (5, 1), (877, 1), (4229, 1), (8377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_877
    · exact prime_4229
    · exact prime_8377
  · decide +kernel

theorem prime_621377880847 : Nat.Prime 621377880847 := by
  apply nodeValid_prime [2, 3, 23, 101, 181, 10709] ⟨621377880847, 5, [(2, 1), (3, 1), (23, 2), (101, 1), (181, 1), (10709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_101
    · exact prime_181
    · exact prime_10709
  · decide +kernel

theorem prime_621377938297 : Nat.Prime 621377938297 := by
  apply nodeValid_prime [2, 3, 73, 118222591] ⟨621377938297, 11, [(2, 3), (3, 2), (73, 1), (118222591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_118222591
  · decide +kernel

theorem prime_622322463827 : Nat.Prime 622322463827 := by
  apply nodeValid_prime [2, 7, 89, 499456231] ⟨622322463827, 2, [(2, 1), (7, 1), (89, 1), (499456231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_89
    · exact prime_499456231
  · decide +kernel

theorem prime_622322527523 : Nat.Prime 622322527523 := by
  apply nodeValid_prime [2, 19, 4493, 3644983] ⟨622322527523, 2, [(2, 1), (19, 1), (4493, 1), (3644983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4493
    · exact prime_3644983
  · decide +kernel

theorem prime_622322528507 : Nat.Prime 622322528507 := by
  apply nodeValid_prime [2, 7, 43, 1033758353] ⟨622322528507, 2, [(2, 1), (7, 1), (43, 1), (1033758353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_43
    · exact prime_1033758353
  · decide +kernel

theorem prime_623267950423 : Nat.Prime 623267950423 := by
  apply nodeValid_prime [2, 3, 13, 19, 32350667] ⟨623267950423, 5, [(2, 1), (3, 1), (13, 2), (19, 1), (32350667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_32350667
  · decide +kernel

theorem prime_623267951653 : Nat.Prime 623267951653 := by
  apply nodeValid_prime [2, 3, 359, 6353, 7591] ⟨623267951653, 5, [(2, 2), (3, 2), (359, 1), (6353, 1), (7591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_359
    · exact prime_6353
    · exact prime_7591
  · decide +kernel

theorem prime_623267958151 : Nat.Prime 623267958151 := by
  apply nodeValid_prime [2, 3, 5, 37, 4159279] ⟨623267958151, 6, [(2, 1), (3, 4), (5, 2), (37, 1), (4159279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_4159279
  · decide +kernel

theorem prime_624214420301 : Nat.Prime 624214420301 := by
  apply nodeValid_prime [2, 5, 167, 37378109] ⟨624214420301, 2, [(2, 2), (5, 2), (167, 1), (37378109, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_167
    · exact prime_37378109
  · decide +kernel

theorem prime_624214422389 : Nat.Prime 624214422389 := by
  apply nodeValid_prime [2, 19, 71, 229, 505157] ⟨624214422389, 2, [(2, 2), (19, 1), (71, 1), (229, 1), (505157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_71
    · exact prime_229
    · exact prime_505157
  · decide +kernel

theorem prime_624214423117 : Nat.Prime 624214423117 := by
  apply nodeValid_prime [2, 3, 5779763177] ⟨624214423117, 2, [(2, 2), (3, 3), (5779763177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5779763177
  · decide +kernel

theorem prime_625161842821 : Nat.Prime 625161842821 := by
  apply nodeValid_prime [2, 3, 5, 21187, 163927] ⟨625161842821, 2, [(2, 2), (3, 2), (5, 1), (21187, 1), (163927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21187
    · exact prime_163927
  · decide +kernel

theorem prime_625161846451 : Nat.Prime 625161846451 := by
  apply nodeValid_prime [2, 3, 5, 29, 461, 311747] ⟨625161846451, 3, [(2, 1), (3, 1), (5, 2), (29, 1), (461, 1), (311747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_461
    · exact prime_311747
  · decide +kernel

theorem prime_625161855613 : Nat.Prime 625161855613 := by
  apply nodeValid_prime [2, 3, 7, 23, 109, 829, 3581] ⟨625161855613, 2, [(2, 2), (3, 1), (7, 1), (23, 1), (109, 1), (829, 1), (3581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
    · exact prime_109
    · exact prime_829
    · exact prime_3581
  · decide +kernel

theorem prime_626110261577 : Nat.Prime 626110261577 := by
  apply nodeValid_prime [2, 479, 163389943] ⟨626110261577, 3, [(2, 3), (479, 1), (163389943, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_163389943
  · decide +kernel

theorem prime_626110275431 : Nat.Prime 626110275431 := by
  apply nodeValid_prime [2, 5, 54673, 1145191] ⟨626110275431, 11, [(2, 1), (5, 1), (54673, 1), (1145191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_54673
    · exact prime_1145191
  · decide +kernel

theorem prime_626110275563 : Nat.Prime 626110275563 := by
  apply nodeValid_prime [2, 19, 23, 67, 2333, 4583] ⟨626110275563, 2, [(2, 1), (19, 1), (23, 1), (67, 1), (2333, 1), (4583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_67
    · exact prime_2333
    · exact prime_4583
  · decide +kernel

theorem prime_627059628161 : Nat.Prime 627059628161 := by
  apply nodeValid_prime [2, 5, 7, 17, 73, 112787] ⟨627059628161, 3, [(2, 7), (5, 1), (7, 1), (17, 1), (73, 1), (112787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_17
    · exact prime_73
    · exact prime_112787
  · decide +kernel

theorem prime_627059628673 : Nat.Prime 627059628673 := by
  apply nodeValid_prime [2, 3, 2003, 815261] ⟨627059628673, 5, [(2, 7), (3, 1), (2003, 1), (815261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2003
    · exact prime_815261
  · decide +kernel

theorem prime_627059645323 : Nat.Prime 627059645323 := by
  apply nodeValid_prime [2, 3, 11, 97, 241, 547, 743] ⟨627059645323, 3, [(2, 1), (3, 1), (11, 1), (97, 1), (241, 1), (547, 1), (743, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_97
    · exact prime_241
    · exact prime_547
    · exact prime_743
  · decide +kernel

theorem prime_628010003939 : Nat.Prime 628010003939 := by
  apply nodeValid_prime [2, 19, 227, 72804313] ⟨628010003939, 2, [(2, 1), (19, 1), (227, 1), (72804313, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_227
    · exact prime_72804313
  · decide +kernel

theorem prime_628010043697 : Nat.Prime 628010043697 := by
  apply nodeValid_prime [2, 3, 7, 79, 1987] ⟨628010043697, 15, [(2, 4), (3, 6), (7, 3), (79, 1), (1987, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_79
    · exact prime_1987
  · decide +kernel

theorem prime_628010043847 : Nat.Prime 628010043847 := by
  apply nodeValid_prime [2, 3, 4451, 23515691] ⟨628010043847, 7, [(2, 1), (3, 1), (4451, 1), (23515691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4451
    · exact prime_23515691
  · decide +kernel

theorem prime_628961305499 : Nat.Prime 628961305499 := by
  apply nodeValid_prime [2, 487, 645750827] ⟨628961305499, 2, [(2, 1), (487, 1), (645750827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_487
    · exact prime_645750827
  · decide +kernel

theorem prime_628961308049 : Nat.Prime 628961308049 := by
  apply nodeValid_prime [2, 39310081753] ⟨628961308049, 3, [(2, 4), (39310081753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_39310081753
  · decide +kernel

theorem prime_628961338987 : Nat.Prime 628961338987 := by
  apply nodeValid_prime [2, 3, 29, 7109, 508471] ⟨628961338987, 3, [(2, 1), (3, 1), (29, 1), (7109, 1), (508471, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_7109
    · exact prime_508471
  · decide +kernel

theorem prime_629913648449 : Nat.Prime 629913648449 := by
  apply nodeValid_prime [2, 7, 1406057251] ⟨629913648449, 3, [(2, 6), (7, 1), (1406057251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1406057251
  · decide +kernel

theorem prime_629913728533 : Nat.Prime 629913728533 := by
  apply nodeValid_prime [2, 3, 11, 47, 997, 101839] ⟨629913728533, 2, [(2, 2), (3, 1), (11, 1), (47, 1), (997, 1), (101839, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_47
    · exact prime_997
    · exact prime_101839
  · decide +kernel

theorem prime_629913729517 : Nat.Prime 629913729517 := by
  apply nodeValid_prime [2, 3, 7103, 7390231] ⟨629913729517, 5, [(2, 2), (3, 1), (7103, 1), (7390231, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7103
    · exact prime_7390231
  · decide +kernel

theorem prime_630866935969 : Nat.Prime 630866935969 := by
  apply nodeValid_prime [2, 3, 23, 285718721] ⟨630866935969, 11, [(2, 5), (3, 1), (23, 1), (285718721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_285718721
  · decide +kernel

theorem prime_630866976449 : Nat.Prime 630866976449 := by
  apply nodeValid_prime [2, 17, 23, 73, 281, 1229] ⟨630866976449, 3, [(2, 6), (17, 1), (23, 1), (73, 1), (281, 1), (1229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_23
    · exact prime_73
    · exact prime_281
    · exact prime_1229
  · decide +kernel

theorem prime_630866977463 : Nat.Prime 630866977463 := by
  apply nodeValid_prime [2, 112247, 2810173] ⟨630866977463, 5, [(2, 1), (112247, 1), (2810173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_112247
    · exact prime_2810173
  · decide +kernel

theorem prime_631821205553 : Nat.Prime 631821205553 := by
  apply nodeValid_prime [2, 65993, 598379] ⟨631821205553, 3, [(2, 4), (65993, 1), (598379, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_65993
    · exact prime_598379
  · decide +kernel

theorem prime_631821206209 : Nat.Prime 631821206209 := by
  apply nodeValid_prime [2, 3, 3290735449] ⟨631821206209, 11, [(2, 6), (3, 1), (3290735449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3290735449
  · decide +kernel

theorem prime_631821206453 : Nat.Prime 631821206453 := by
  apply nodeValid_prime [2, 19, 8313436927] ⟨631821206453, 2, [(2, 2), (19, 1), (8313436927, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_8313436927
  · decide +kernel

theorem prime_632776456639 : Nat.Prime 632776456639 := by
  apply nodeValid_prime [2, 3, 35154247591] ⟨632776456639, 3, [(2, 1), (3, 2), (35154247591, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_35154247591
  · decide +kernel

theorem prime_632776467931 : Nat.Prime 632776467931 := by
  apply nodeValid_prime [2, 3, 5, 21092548931] ⟨632776467931, 2, [(2, 1), (3, 1), (5, 1), (21092548931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_21092548931
  · decide +kernel

theorem prime_632776468063 : Nat.Prime 632776468063 := by
  apply nodeValid_prime [2, 3, 105462744677] ⟨632776468063, 3, [(2, 1), (3, 1), (105462744677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_105462744677
  · decide +kernel

theorem prime_633732680291 : Nat.Prime 633732680291 := by
  apply nodeValid_prime [2, 5, 63373268029] ⟨633732680291, 2, [(2, 1), (5, 1), (63373268029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_63373268029
  · decide +kernel

theorem prime_633732714259 : Nat.Prime 633732714259 := by
  apply nodeValid_prime [2, 3, 7, 19, 2971, 267301] ⟨633732714259, 2, [(2, 1), (3, 1), (7, 1), (19, 1), (2971, 1), (267301, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_2971
    · exact prime_267301
  · decide +kernel

theorem prime_633732719371 : Nat.Prime 633732719371 := by
  apply nodeValid_prime [2, 3, 5, 7193, 2936803] ⟨633732719371, 11, [(2, 1), (3, 1), (5, 1), (7193, 1), (2936803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7193
    · exact prime_2936803
  · decide +kernel

theorem prime_634689885139 : Nat.Prime 634689885139 := by
  apply nodeValid_prime [2, 3, 83, 1274477681] ⟨634689885139, 3, [(2, 1), (3, 1), (83, 1), (1274477681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_1274477681
  · decide +kernel

theorem prime_634689892891 : Nat.Prime 634689892891 := by
  apply nodeValid_prime [2, 3, 5, 41, 19111409] ⟨634689892891, 3, [(2, 1), (3, 4), (5, 1), (41, 1), (19111409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_19111409
  · decide +kernel

theorem prime_634689892919 : Nat.Prime 634689892919 := by
  apply nodeValid_prime [2, 317344946459] ⟨634689892919, 11, [(2, 1), (317344946459, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_317344946459
  · decide +kernel

theorem prime_635648074099 : Nat.Prime 635648074099 := by
  apply nodeValid_prime [2, 3, 316223, 335021] ⟨635648074099, 2, [(2, 1), (3, 1), (316223, 1), (335021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_316223
    · exact prime_335021
  · decide +kernel

theorem prime_635648082001 : Nat.Prime 635648082001 := by
  apply nodeValid_prime [2, 3, 5, 105941347] ⟨635648082001, 23, [(2, 4), (3, 1), (5, 3), (105941347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_105941347
  · decide +kernel

theorem prime_635648082367 : Nat.Prime 635648082367 := by
  apply nodeValid_prime [2, 3, 11, 317, 30381803] ⟨635648082367, 6, [(2, 1), (3, 1), (11, 1), (317, 1), (30381803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_317
    · exact prime_30381803
  · decide +kernel

theorem prime_636607237687 : Nat.Prime 636607237687 := by
  apply nodeValid_prime [2, 3, 7, 331, 45792493] ⟨636607237687, 5, [(2, 1), (3, 1), (7, 1), (331, 1), (45792493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_331
    · exact prime_45792493
  · decide +kernel

theorem prime_636607245137 : Nat.Prime 636607245137 := by
  apply nodeValid_prime [2, 17, 967, 2420339] ⟨636607245137, 3, [(2, 4), (17, 1), (967, 1), (2420339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_967
    · exact prime_2420339
  · decide +kernel

theorem prime_637567378277 : Nat.Prime 637567378277 := by
  apply nodeValid_prime [2, 17, 19, 43, 1301, 8821] ⟨637567378277, 2, [(2, 2), (17, 1), (19, 1), (43, 1), (1301, 1), (8821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_43
    · exact prime_1301
    · exact prime_8821
  · decide +kernel

theorem prime_637567380209 : Nat.Prime 637567380209 := by
  apply nodeValid_prime [2, 11, 691, 1451, 3613] ⟨637567380209, 3, [(2, 4), (11, 1), (691, 1), (1451, 1), (3613, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_691
    · exact prime_1451
    · exact prime_3613
  · decide +kernel

theorem prime_637567382663 : Nat.Prime 637567382663 := by
  apply nodeValid_prime [2, 7, 17, 43, 349, 3643] ⟨637567382663, 5, [(2, 1), (7, 3), (17, 1), (43, 1), (349, 1), (3643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_43
    · exact prime_349
    · exact prime_3643
  · decide +kernel

theorem prime_638528513963 : Nat.Prime 638528513963 := by
  apply nodeValid_prime [2, 319264256981] ⟨638528513963, 2, [(2, 1), (319264256981, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_319264256981
  · decide +kernel

theorem prime_638528524099 : Nat.Prime 638528524099 := by
  apply nodeValid_prime [2, 3, 191, 557180213] ⟨638528524099, 2, [(2, 1), (3, 1), (191, 1), (557180213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_557180213
  · decide +kernel

theorem prime_638528525903 : Nat.Prime 638528525903 := by
  apply nodeValid_prime [2, 67, 4765138253] ⟨638528525903, 5, [(2, 1), (67, 1), (4765138253, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_4765138253
  · decide +kernel

theorem prime_639490625321 : Nat.Prime 639490625321 := by
  apply nodeValid_prime [2, 5, 15987265633] ⟨639490625321, 6, [(2, 3), (5, 1), (15987265633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_15987265633
  · decide +kernel

theorem prime_639490651099 : Nat.Prime 639490651099 := by
  apply nodeValid_prime [2, 3, 13, 29, 839, 336961] ⟨639490651099, 3, [(2, 1), (3, 1), (13, 1), (29, 1), (839, 1), (336961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_839
    · exact prime_336961
  · decide +kernel

theorem prime_639490652237 : Nat.Prime 639490652237 := by
  apply nodeValid_prime [2, 159872663059] ⟨639490652237, 2, [(2, 2), (159872663059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_159872663059
  · decide +kernel

theorem prime_640453715413 : Nat.Prime 640453715413 := by
  apply nodeValid_prime [2, 3, 7, 37, 47, 626341] ⟨640453715413, 2, [(2, 2), (3, 1), (7, 2), (37, 1), (47, 1), (626341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37
    · exact prime_47
    · exact prime_626341
  · decide +kernel

theorem prime_640453716577 : Nat.Prime 640453716577 := by
  apply nodeValid_prime [2, 3, 17891, 124297] ⟨640453716577, 5, [(2, 5), (3, 2), (17891, 1), (124297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17891
    · exact prime_124297
  · decide +kernel

theorem prime_640453717313 : Nat.Prime 640453717313 := by
  apply nodeValid_prime [2, 127, 179, 479, 919] ⟨640453717313, 3, [(2, 6), (127, 1), (179, 1), (479, 1), (919, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_127
    · exact prime_179
    · exact prime_479
    · exact prime_919
  · decide +kernel

theorem prime_641417768021 : Nat.Prime 641417768021 := by
  apply nodeValid_prime [2, 5, 293, 109456957] ⟨641417768021, 2, [(2, 2), (5, 1), (293, 1), (109456957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_293
    · exact prime_109456957
  · decide +kernel

theorem prime_641417768567 : Nat.Prime 641417768567 := by
  apply nodeValid_prime [2, 126851, 2528233] ⟨641417768567, 5, [(2, 1), (126851, 1), (2528233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_126851
    · exact prime_2528233
  · decide +kernel

theorem prime_641417791691 : Nat.Prime 641417791691 := by
  apply nodeValid_prime [2, 5, 13, 43, 739, 155269] ⟨641417791691, 14, [(2, 1), (5, 1), (13, 1), (43, 1), (739, 1), (155269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_43
    · exact prime_739
    · exact prime_155269
  · decide +kernel

theorem prime_642382855921 : Nat.Prime 642382855921 := by
  apply nodeValid_prime [2, 3, 5, 13, 6991, 9817] ⟨642382855921, 23, [(2, 4), (3, 2), (5, 1), (13, 1), (6991, 1), (9817, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_6991
    · exact prime_9817
  · decide +kernel

theorem prime_642382856179 : Nat.Prime 642382856179 := by
  apply nodeValid_prime [2, 3, 7, 17, 899695877] ⟨642382856179, 2, [(2, 1), (3, 1), (7, 1), (17, 1), (899695877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_899695877
  · decide +kernel

theorem prime_642382856597 : Nat.Prime 642382856597 := by
  apply nodeValid_prime [2, 13, 12353516473] ⟨642382856597, 2, [(2, 2), (13, 1), (12353516473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_12353516473
  · decide +kernel

end Sude.Lucas.Generated
