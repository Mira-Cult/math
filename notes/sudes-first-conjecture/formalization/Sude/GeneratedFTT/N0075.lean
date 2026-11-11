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
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0020
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0025
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0031
import Sude.GeneratedFTT.N0033
import Sude.GeneratedFTT.N0035
import Sude.GeneratedFTT.N0036
import Sude.GeneratedFTT.N0037
import Sude.GeneratedFTT.N0039
import Sude.GeneratedFTT.N0042
import Sude.GeneratedFTT.N0045
import Sude.GeneratedFTT.N0049
import Sude.GeneratedFTT.N0051
import Sude.GeneratedFTT.N0055
import Sude.GeneratedFTT.N0056
import Sude.GeneratedFTT.N0058
import Sude.GeneratedFTT.N0060
import Sude.GeneratedFTT.N0062
import Sude.GeneratedFTT.N0065
import Sude.GeneratedFTT.N0066
import Sude.GeneratedFTT.N0072

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_10303 : Nat.Prime 10303 := by
  apply nodeValid_prime [2, 3, 17, 101] ⟨10303, 3, [(2, 1), (3, 1), (17, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_101
  · decide +kernel

theorem prime_19211 : Nat.Prime 19211 := by
  apply nodeValid_prime [2, 5, 17, 113] ⟨19211, 6, [(2, 1), (5, 1), (17, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_113
  · decide +kernel

theorem prime_24329 : Nat.Prime 24329 := by
  apply nodeValid_prime [2, 3041] ⟨24329, 3, [(2, 3), (3041, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3041
  · decide +kernel

theorem prime_24989 : Nat.Prime 24989 := by
  apply nodeValid_prime [2, 6247] ⟨24989, 2, [(2, 2), (6247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_6247
  · decide +kernel

theorem prime_25717 : Nat.Prime 25717 := by
  apply nodeValid_prime [2, 3, 2143] ⟨25717, 2, [(2, 2), (3, 1), (2143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2143
  · decide +kernel

theorem prime_27733 : Nat.Prime 27733 := by
  apply nodeValid_prime [2, 3, 2311] ⟨27733, 2, [(2, 2), (3, 1), (2311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2311
  · decide +kernel

theorem prime_28541 : Nat.Prime 28541 := by
  apply nodeValid_prime [2, 5, 1427] ⟨28541, 2, [(2, 2), (5, 1), (1427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1427
  · decide +kernel

theorem prime_28933 : Nat.Prime 28933 := by
  apply nodeValid_prime [2, 3, 2411] ⟨28933, 2, [(2, 2), (3, 1), (2411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2411
  · decide +kernel

theorem prime_29387 : Nat.Prime 29387 := by
  apply nodeValid_prime [2, 7, 2099] ⟨29387, 2, [(2, 1), (7, 1), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2099
  · decide +kernel

theorem prime_35027 : Nat.Prime 35027 := by
  apply nodeValid_prime [2, 83, 211] ⟨35027, 2, [(2, 1), (83, 1), (211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_211
  · decide +kernel

theorem prime_37783 : Nat.Prime 37783 := by
  apply nodeValid_prime [2, 3, 2099] ⟨37783, 3, [(2, 1), (3, 2), (2099, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2099
  · decide +kernel

theorem prime_38669 : Nat.Prime 38669 := by
  apply nodeValid_prime [2, 7, 1381] ⟨38669, 2, [(2, 2), (7, 1), (1381, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1381
  · decide +kernel

theorem prime_41213 : Nat.Prime 41213 := by
  apply nodeValid_prime [2, 10303] ⟨41213, 2, [(2, 2), (10303, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_10303
  · decide +kernel

theorem prime_41549 : Nat.Prime 41549 := by
  apply nodeValid_prime [2, 13, 17, 47] ⟨41549, 3, [(2, 2), (13, 1), (17, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
    · exact prime_47
  · decide +kernel

theorem prime_43579 : Nat.Prime 43579 := by
  apply nodeValid_prime [2, 3, 269] ⟨43579, 2, [(2, 1), (3, 4), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_269
  · decide +kernel

theorem prime_55721 : Nat.Prime 55721 := by
  apply nodeValid_prime [2, 5, 7, 199] ⟨55721, 3, [(2, 3), (5, 1), (7, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_199
  · decide +kernel

theorem prime_68261 : Nat.Prime 68261 := by
  apply nodeValid_prime [2, 5, 3413] ⟨68261, 2, [(2, 2), (5, 1), (3413, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3413
  · decide +kernel

theorem prime_72269 : Nat.Prime 72269 := by
  apply nodeValid_prime [2, 7, 29, 89] ⟨72269, 3, [(2, 2), (7, 1), (29, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_89
  · decide +kernel

theorem prime_77339 : Nat.Prime 77339 := by
  apply nodeValid_prime [2, 38669] ⟨77339, 2, [(2, 1), (38669, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_38669
  · decide +kernel

theorem prime_89227 : Nat.Prime 89227 := by
  apply nodeValid_prime [2, 3, 4957] ⟨89227, 3, [(2, 1), (3, 2), (4957, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4957
  · decide +kernel

theorem prime_108401 : Nat.Prime 108401 := by
  apply nodeValid_prime [2, 5, 271] ⟨108401, 3, [(2, 4), (5, 2), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
  · decide +kernel

theorem prime_116461 : Nat.Prime 116461 := by
  apply nodeValid_prime [2, 3, 5, 647] ⟨116461, 2, [(2, 2), (3, 2), (5, 1), (647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_647
  · decide +kernel

theorem prime_132547 : Nat.Prime 132547 := by
  apply nodeValid_prime [2, 3, 22091] ⟨132547, 2, [(2, 1), (3, 1), (22091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_22091
  · decide +kernel

theorem prime_137933 : Nat.Prime 137933 := by
  apply nodeValid_prime [2, 34483] ⟨137933, 2, [(2, 2), (34483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_34483
  · decide +kernel

theorem prime_138731 : Nat.Prime 138731 := by
  apply nodeValid_prime [2, 5, 13873] ⟨138731, 6, [(2, 1), (5, 1), (13873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13873
  · decide +kernel

theorem prime_140123 : Nat.Prime 140123 := by
  apply nodeValid_prime [2, 70061] ⟨140123, 2, [(2, 1), (70061, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_70061
  · decide +kernel

theorem prime_144539 : Nat.Prime 144539 := by
  apply nodeValid_prime [2, 72269] ⟨144539, 2, [(2, 1), (72269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_72269
  · decide +kernel

theorem prime_145021 : Nat.Prime 145021 := by
  apply nodeValid_prime [2, 3, 5, 2417] ⟨145021, 2, [(2, 2), (3, 1), (5, 1), (2417, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2417
  · decide +kernel

theorem prime_145121 : Nat.Prime 145121 := by
  apply nodeValid_prime [2, 5, 907] ⟨145121, 3, [(2, 5), (5, 1), (907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_907
  · decide +kernel

theorem prime_172517 : Nat.Prime 172517 := by
  apply nodeValid_prime [2, 17, 43, 59] ⟨172517, 2, [(2, 2), (17, 1), (43, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_43
    · exact prime_59
  · decide +kernel

theorem prime_213481 : Nat.Prime 213481 := by
  apply nodeValid_prime [2, 3, 5, 593] ⟨213481, 13, [(2, 3), (3, 2), (5, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_593
  · decide +kernel

theorem prime_219433 : Nat.Prime 219433 := by
  apply nodeValid_prime [2, 3, 41, 223] ⟨219433, 5, [(2, 3), (3, 1), (41, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_223
  · decide +kernel

theorem prime_232961 : Nat.Prime 232961 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨232961, 12, [(2, 9), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_246391 : Nat.Prime 246391 := by
  apply nodeValid_prime [2, 3, 5, 43, 191] ⟨246391, 3, [(2, 1), (3, 1), (5, 1), (43, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_191
  · decide +kernel

theorem prime_252949 : Nat.Prime 252949 := by
  apply nodeValid_prime [2, 3, 107, 197] ⟨252949, 2, [(2, 2), (3, 1), (107, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_197
  · decide +kernel

theorem prime_270239 : Nat.Prime 270239 := by
  apply nodeValid_prime [2, 135119] ⟨270239, 7, [(2, 1), (135119, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_135119
  · decide +kernel

theorem prime_287297 : Nat.Prime 287297 := by
  apply nodeValid_prime [2, 67] ⟨287297, 3, [(2, 6), (67, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67
  · decide +kernel

theorem prime_300721 : Nat.Prime 300721 := by
  apply nodeValid_prime [2, 3, 5, 7, 179] ⟨300721, 13, [(2, 4), (3, 1), (5, 1), (7, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_179
  · decide +kernel

theorem prime_327263 : Nat.Prime 327263 := by
  apply nodeValid_prime [2, 13, 41, 307] ⟨327263, 10, [(2, 1), (13, 1), (41, 1), (307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_41
    · exact prime_307
  · decide +kernel

theorem prime_332393 : Nat.Prime 332393 := by
  apply nodeValid_prime [2, 41549] ⟨332393, 3, [(2, 3), (41549, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41549
  · decide +kernel

theorem prime_342547 : Nat.Prime 342547 := by
  apply nodeValid_prime [2, 3, 37, 1543] ⟨342547, 2, [(2, 1), (3, 1), (37, 1), (1543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_1543
  · decide +kernel

theorem prime_384589 : Nat.Prime 384589 := by
  apply nodeValid_prime [2, 3, 1187] ⟨384589, 2, [(2, 2), (3, 4), (1187, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1187
  · decide +kernel

theorem prime_481681 : Nat.Prime 481681 := by
  apply nodeValid_prime [2, 3, 5, 223] ⟨481681, 11, [(2, 4), (3, 3), (5, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_223
  · decide +kernel

theorem prime_522497 : Nat.Prime 522497 := by
  apply nodeValid_prime [2, 13, 157] ⟨522497, 5, [(2, 8), (13, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_157
  · decide +kernel

theorem prime_570821 : Nat.Prime 570821 := by
  apply nodeValid_prime [2, 5, 28541] ⟨570821, 2, [(2, 2), (5, 1), (28541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_28541
  · decide +kernel

theorem prime_578789 : Nat.Prime 578789 := by
  apply nodeValid_prime [2, 7, 2953] ⟨578789, 2, [(2, 2), (7, 2), (2953, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2953
  · decide +kernel

theorem prime_614753 : Nat.Prime 614753 := by
  apply nodeValid_prime [2, 19211] ⟨614753, 3, [(2, 5), (19211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_19211
  · decide +kernel

theorem prime_616367 : Nat.Prime 616367 := by
  apply nodeValid_prime [2, 29, 10627] ⟨616367, 5, [(2, 1), (29, 1), (10627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_10627
  · decide +kernel

theorem prime_658261 : Nat.Prime 658261 := by
  apply nodeValid_prime [2, 3, 5, 23, 53] ⟨658261, 2, [(2, 2), (3, 3), (5, 1), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_681137 : Nat.Prime 681137 := by
  apply nodeValid_prime [2, 42571] ⟨681137, 3, [(2, 4), (42571, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42571
  · decide +kernel

theorem prime_711371 : Nat.Prime 711371 := by
  apply nodeValid_prime [2, 5, 11, 29, 223] ⟨711371, 10, [(2, 1), (5, 1), (11, 1), (29, 1), (223, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_223
  · decide +kernel

theorem prime_855431 : Nat.Prime 855431 := by
  apply nodeValid_prime [2, 5, 131, 653] ⟨855431, 11, [(2, 1), (5, 1), (131, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_653
  · decide +kernel

theorem prime_870127 : Nat.Prime 870127 := by
  apply nodeValid_prime [2, 3, 145021] ⟨870127, 3, [(2, 1), (3, 1), (145021, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_145021
  · decide +kernel

theorem prime_1216451 : Nat.Prime 1216451 := by
  apply nodeValid_prime [2, 5, 24329] ⟨1216451, 6, [(2, 1), (5, 2), (24329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_24329
  · decide +kernel

theorem prime_1326137 : Nat.Prime 1326137 := by
  apply nodeValid_prime [2, 7, 17, 199] ⟨1326137, 3, [(2, 3), (7, 2), (17, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_199
  · decide +kernel

theorem prime_1572433 : Nat.Prime 1572433 := by
  apply nodeValid_prime [2, 3, 17, 41, 47] ⟨1572433, 10, [(2, 4), (3, 1), (17, 1), (41, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_41
    · exact prime_47
  · decide +kernel

theorem prime_1595051 : Nat.Prime 1595051 := by
  apply nodeValid_prime [2, 5, 19, 23, 73] ⟨1595051, 2, [(2, 1), (5, 2), (19, 1), (23, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_23
    · exact prime_73
  · decide +kernel

theorem prime_1741469 : Nat.Prime 1741469 := by
  apply nodeValid_prime [2, 23, 823] ⟨1741469, 3, [(2, 2), (23, 2), (823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_823
  · decide +kernel

theorem prime_2380633 : Nat.Prime 2380633 := by
  apply nodeValid_prime [2, 3, 281, 353] ⟨2380633, 5, [(2, 3), (3, 1), (281, 1), (353, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_353
  · decide +kernel

theorem prime_2531989 : Nat.Prime 2531989 := by
  apply nodeValid_prime [2, 3, 61, 1153] ⟨2531989, 2, [(2, 2), (3, 2), (61, 1), (1153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_61
    · exact prime_1153
  · decide +kernel

theorem prime_2562143 : Nat.Prime 2562143 := by
  apply nodeValid_prime [2, 11, 116461] ⟨2562143, 5, [(2, 1), (11, 1), (116461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_116461
  · decide +kernel

theorem prime_2925463 : Nat.Prime 2925463 := by
  apply nodeValid_prime [2, 3, 17, 23, 29, 43] ⟨2925463, 3, [(2, 1), (3, 1), (17, 1), (23, 1), (29, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_23
    · exact prime_29
    · exact prime_43
  · decide +kernel

theorem prime_3368003 : Nat.Prime 3368003 := by
  apply nodeValid_prime [2, 11, 29, 5279] ⟨3368003, 2, [(2, 1), (11, 1), (29, 1), (5279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_5279
  · decide +kernel

theorem prime_3526441 : Nat.Prime 3526441 := by
  apply nodeValid_prime [2, 3, 5, 29387] ⟨3526441, 11, [(2, 3), (3, 1), (5, 1), (29387, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29387
  · decide +kernel

theorem prime_4547239 : Nat.Prime 4547239 := by
  apply nodeValid_prime [2, 3, 23, 83, 397] ⟨4547239, 6, [(2, 1), (3, 1), (23, 1), (83, 1), (397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_83
    · exact prime_397
  · decide +kernel

theorem prime_4696583 : Nat.Prime 4696583 := by
  apply nodeValid_prime [2, 11, 213481] ⟨4696583, 5, [(2, 1), (11, 1), (213481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_213481
  · decide +kernel

theorem prime_5849939 : Nat.Prime 5849939 := by
  apply nodeValid_prime [2, 17, 29, 349] ⟨5849939, 2, [(2, 1), (17, 2), (29, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_349
  · decide +kernel

theorem prime_6352013 : Nat.Prime 6352013 := by
  apply nodeValid_prime [2, 37, 167, 257] ⟨6352013, 2, [(2, 2), (37, 1), (167, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_167
    · exact prime_257
  · decide +kernel

theorem prime_6471511 : Nat.Prime 6471511 := by
  apply nodeValid_prime [2, 3, 5, 23, 83, 113] ⟨6471511, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (83, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_83
    · exact prime_113
  · decide +kernel

theorem prime_6922603 : Nat.Prime 6922603 := by
  apply nodeValid_prime [2, 3, 384589] ⟨6922603, 2, [(2, 1), (3, 2), (384589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_384589
  · decide +kernel

theorem prime_6960799 : Nat.Prime 6960799 := by
  apply nodeValid_prime [2, 3, 13, 151, 197] ⟨6960799, 3, [(2, 1), (3, 2), (13, 1), (151, 1), (197, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_151
    · exact prime_197
  · decide +kernel

theorem prime_7821643 : Nat.Prime 7821643 := by
  apply nodeValid_prime [2, 3, 101, 12907] ⟨7821643, 5, [(2, 1), (3, 1), (101, 1), (12907, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
    · exact prime_12907
  · decide +kernel

theorem prime_10418203 : Nat.Prime 10418203 := by
  apply nodeValid_prime [2, 3, 578789] ⟨10418203, 2, [(2, 1), (3, 2), (578789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_578789
  · decide +kernel

theorem prime_10615043 : Nat.Prime 10615043 := by
  apply nodeValid_prime [2, 107, 49603] ⟨10615043, 2, [(2, 1), (107, 1), (49603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_49603
  · decide +kernel

theorem prime_11699879 : Nat.Prime 11699879 := by
  apply nodeValid_prime [2, 5849939] ⟨11699879, 7, [(2, 1), (5849939, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5849939
  · decide +kernel

theorem prime_13269973 : Nat.Prime 13269973 := by
  apply nodeValid_prime [2, 3, 43, 25717] ⟨13269973, 2, [(2, 2), (3, 1), (43, 1), (25717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_25717
  · decide +kernel

theorem prime_13678211 : Nat.Prime 13678211 := by
  apply nodeValid_prime [2, 5, 7, 13, 15031] ⟨13678211, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (15031, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_15031
  · decide +kernel

theorem prime_14499857 : Nat.Prime 14499857 := by
  apply nodeValid_prime [2, 7, 37, 3499] ⟨14499857, 3, [(2, 4), (7, 1), (37, 1), (3499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_3499
  · decide +kernel

theorem prime_20076587 : Nat.Prime 20076587 := by
  apply nodeValid_prime [2, 79, 283, 449] ⟨20076587, 2, [(2, 1), (79, 1), (283, 1), (449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_283
    · exact prime_449
  · decide +kernel

theorem prime_21353711 : Nat.Prime 21353711 := by
  apply nodeValid_prime [2, 5, 7, 43579] ⟨21353711, 7, [(2, 1), (5, 1), (7, 2), (43579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43579
  · decide +kernel

theorem prime_23006537 : Nat.Prime 23006537 := by
  apply nodeValid_prime [2, 7, 311, 1321] ⟨23006537, 3, [(2, 3), (7, 1), (311, 1), (1321, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_311
    · exact prime_1321
  · decide +kernel

theorem prime_23399759 : Nat.Prime 23399759 := by
  apply nodeValid_prime [2, 11699879] ⟨23399759, 11, [(2, 1), (11699879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11699879
  · decide +kernel

theorem prime_26589257 : Nat.Prime 26589257 := by
  apply nodeValid_prime [2, 311, 10687] ⟨26589257, 3, [(2, 3), (311, 1), (10687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_311
    · exact prime_10687
  · decide +kernel

theorem prime_27356423 : Nat.Prime 27356423 := by
  apply nodeValid_prime [2, 13678211] ⟨27356423, 5, [(2, 1), (13678211, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13678211
  · decide +kernel

theorem prime_31627727 : Nat.Prime 31627727 := by
  apply nodeValid_prime [2, 13, 1216451] ⟨31627727, 5, [(2, 1), (13, 1), (1216451, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_1216451
  · decide +kernel

theorem prime_33283819 : Nat.Prime 33283819 := by
  apply nodeValid_prime [2, 3, 616367] ⟨33283819, 2, [(2, 1), (3, 3), (616367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_616367
  · decide +kernel

theorem prime_44006177 : Nat.Prime 44006177 := by
  apply nodeValid_prime [2, 23, 59791] ⟨44006177, 3, [(2, 5), (23, 1), (59791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_59791
  · decide +kernel

theorem prime_45986659 : Nat.Prime 45986659 := by
  apply nodeValid_prime [2, 3, 1787, 4289] ⟨45986659, 10, [(2, 1), (3, 1), (1787, 1), (4289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1787
    · exact prime_4289
  · decide +kernel

theorem prime_56902123 : Nat.Prime 56902123 := by
  apply nodeValid_prime [2, 3, 173, 6091] ⟨56902123, 2, [(2, 1), (3, 3), (173, 1), (6091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_173
    · exact prime_6091
  · decide +kernel

theorem prime_62509219 : Nat.Prime 62509219 := by
  apply nodeValid_prime [2, 3, 10418203] ⟨62509219, 2, [(2, 1), (3, 1), (10418203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10418203
  · decide +kernel

theorem prime_70097383 : Nat.Prime 70097383 := by
  apply nodeValid_prime [2, 3, 191, 20389] ⟨70097383, 5, [(2, 1), (3, 2), (191, 1), (20389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_20389
  · decide +kernel

theorem prime_81521827 : Nat.Prime 81521827 := by
  apply nodeValid_prime [2, 3, 653, 20807] ⟨81521827, 2, [(2, 1), (3, 1), (653, 1), (20807, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_653
    · exact prime_20807
  · decide +kernel

theorem prime_102885199 : Nat.Prime 102885199 := by
  apply nodeValid_prime [2, 3, 13, 239, 5519] ⟨102885199, 6, [(2, 1), (3, 1), (13, 1), (239, 1), (5519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_239
    · exact prime_5519
  · decide +kernel

theorem prime_106172707 : Nat.Prime 106172707 := by
  apply nodeValid_prime [2, 3, 31, 570821] ⟨106172707, 7, [(2, 1), (3, 1), (31, 1), (570821, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_570821
  · decide +kernel

theorem prime_120569951 : Nat.Prime 120569951 := by
  apply nodeValid_prime [2, 5, 17, 83, 1709] ⟨120569951, 13, [(2, 1), (5, 2), (17, 1), (83, 1), (1709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_83
    · exact prime_1709
  · decide +kernel

theorem prime_123995581 : Nat.Prime 123995581 := by
  apply nodeValid_prime [2, 3, 5, 59, 35027] ⟨123995581, 2, [(2, 2), (3, 1), (5, 1), (59, 1), (35027, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_59
    · exact prime_35027
  · decide +kernel

theorem prime_138579823 : Nat.Prime 138579823 := by
  apply nodeValid_prime [2, 3, 855431] ⟨138579823, 3, [(2, 1), (3, 4), (855431, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_855431
  · decide +kernel

theorem prime_229074829 : Nat.Prime 229074829 := by
  apply nodeValid_prime [2, 3, 29, 658261] ⟨229074829, 2, [(2, 2), (3, 1), (29, 1), (658261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_658261
  · decide +kernel

theorem prime_374577823 : Nat.Prime 374577823 := by
  apply nodeValid_prime [2, 3, 157, 132547] ⟨374577823, 5, [(2, 1), (3, 2), (157, 1), (132547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_157
    · exact prime_132547
  · decide +kernel

theorem prime_415356181 : Nat.Prime 415356181 := by
  apply nodeValid_prime [2, 3, 5, 6922603] ⟨415356181, 6, [(2, 2), (3, 1), (5, 1), (6922603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_6922603
  · decide +kernel

theorem prime_547179277 : Nat.Prime 547179277 := by
  apply nodeValid_prime [2, 3, 7, 41, 22697] ⟨547179277, 2, [(2, 2), (3, 1), (7, 2), (41, 1), (22697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_41
    · exact prime_22697
  · decide +kernel

theorem prime_822204941 : Nat.Prime 822204941 := by
  apply nodeValid_prime [2, 5, 31, 1326137] ⟨822204941, 2, [(2, 2), (5, 1), (31, 1), (1326137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_1326137
  · decide +kernel

theorem prime_916299317 : Nat.Prime 916299317 := by
  apply nodeValid_prime [2, 229074829] ⟨916299317, 2, [(2, 2), (229074829, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_229074829
  · decide +kernel

theorem prime_936767311 : Nat.Prime 936767311 := by
  apply nodeValid_prime [2, 3, 5, 181, 172517] ⟨936767311, 6, [(2, 1), (3, 1), (5, 1), (181, 1), (172517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
    · exact prime_172517
  · decide +kernel

theorem prime_1138598173 : Nat.Prime 1138598173 := by
  apply nodeValid_prime [2, 3, 31627727] ⟨1138598173, 2, [(2, 2), (3, 2), (31627727, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31627727
  · decide +kernel

theorem prime_1177676587 : Nat.Prime 1177676587 := by
  apply nodeValid_prime [2, 3, 191, 342547] ⟨1177676587, 3, [(2, 1), (3, 2), (191, 1), (342547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_342547
  · decide +kernel

theorem prime_1477246843 : Nat.Prime 1477246843 := by
  apply nodeValid_prime [2, 3, 27356423] ⟨1477246843, 3, [(2, 1), (3, 3), (27356423, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_27356423
  · decide +kernel

theorem prime_1498311293 : Nat.Prime 1498311293 := by
  apply nodeValid_prime [2, 374577823] ⟨1498311293, 2, [(2, 2), (374577823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_374577823
  · decide +kernel

theorem prime_1629339893 : Nat.Prime 1629339893 := by
  apply nodeValid_prime [2, 9791, 41603] ⟨1629339893, 2, [(2, 2), (9791, 1), (41603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9791
    · exact prime_41603
  · decide +kernel

theorem prime_1908304949 : Nat.Prime 1908304949 := by
  apply nodeValid_prime [2, 11, 1499, 28933] ⟨1908304949, 2, [(2, 2), (11, 1), (1499, 1), (28933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_1499
    · exact prime_28933
  · decide +kernel

theorem prime_2188826737 : Nat.Prime 2188826737 := by
  apply nodeValid_prime [2, 3, 29, 1572433] ⟨2188826737, 7, [(2, 4), (3, 1), (29, 1), (1572433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_1572433
  · decide +kernel

theorem prime_2549925773 : Nat.Prime 2549925773 := by
  apply nodeValid_prime [2, 20051, 31793] ⟨2549925773, 2, [(2, 2), (20051, 1), (31793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_20051
    · exact prime_31793
  · decide +kernel

theorem prime_3518171941 : Nat.Prime 3518171941 := by
  apply nodeValid_prime [2, 3, 5, 859, 68261] ⟨3518171941, 6, [(2, 2), (3, 1), (5, 1), (859, 1), (68261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_859
    · exact prime_68261
  · decide +kernel

theorem prime_4076565797 : Nat.Prime 4076565797 := by
  apply nodeValid_prime [2, 17, 3526441] ⟨4076565797, 2, [(2, 2), (17, 2), (3526441, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_3526441
  · decide +kernel

theorem prime_4157394691 : Nat.Prime 4157394691 := by
  apply nodeValid_prime [2, 3, 5, 138579823] ⟨4157394691, 12, [(2, 1), (3, 1), (5, 1), (138579823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_138579823
  · decide +kernel

theorem prime_4286914243 : Nat.Prime 4286914243 := by
  apply nodeValid_prime [2, 3, 13, 17, 197, 16411] ⟨4286914243, 3, [(2, 1), (3, 1), (13, 1), (17, 1), (197, 1), (16411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_17
    · exact prime_197
    · exact prime_16411
  · decide +kernel

theorem prime_4616825149 : Nat.Prime 4616825149 := by
  apply nodeValid_prime [2, 3, 13, 252949] ⟨4616825149, 2, [(2, 2), (3, 3), (13, 2), (252949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_252949
  · decide +kernel

theorem prime_5915941657 : Nat.Prime 5915941657 := by
  apply nodeValid_prime [2, 3, 17, 14499857] ⟨5915941657, 5, [(2, 3), (3, 1), (17, 1), (14499857, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_14499857
  · decide +kernel

theorem prime_7117695131 : Nat.Prime 7117695131 := by
  apply nodeValid_prime [2, 5, 7, 13, 7821643] ⟨7117695131, 2, [(2, 1), (5, 1), (7, 1), (13, 1), (7821643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_7821643
  · decide +kernel

theorem prime_7479611693 : Nat.Prime 7479611693 := by
  apply nodeValid_prime [2, 7, 307, 870127] ⟨7479611693, 2, [(2, 2), (7, 1), (307, 1), (870127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_307
    · exact prime_870127
  · decide +kernel

theorem prime_14204520793 : Nat.Prime 14204520793 := by
  apply nodeValid_prime [2, 3, 7, 11, 2562143] ⟨14204520793, 5, [(2, 3), (3, 2), (7, 1), (11, 1), (2562143, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_2562143
  · decide +kernel

theorem prime_26716269287 : Nat.Prime 26716269287 := by
  apply nodeValid_prime [2, 7, 1908304949] ⟨26716269287, 5, [(2, 1), (7, 1), (1908304949, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1908304949
  · decide +kernel

theorem prime_28880521897 : Nat.Prime 28880521897 := by
  apply nodeValid_prime [2, 3, 691, 1741469] ⟨28880521897, 5, [(2, 3), (3, 1), (691, 1), (1741469, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
    · exact prime_1741469
  · decide +kernel

theorem prime_29547680959 : Nat.Prime 29547680959 := by
  apply nodeValid_prime [2, 3, 547179277] ⟨29547680959, 11, [(2, 1), (3, 3), (547179277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_547179277
  · decide +kernel

theorem prime_46200776411 : Nat.Prime 46200776411 := by
  apply nodeValid_prime [2, 5, 17, 1103, 246391] ⟨46200776411, 2, [(2, 1), (5, 1), (17, 1), (1103, 1), (246391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_1103
    · exact prime_246391
  · decide +kernel

theorem prime_57824116579 : Nat.Prime 57824116579 := by
  apply nodeValid_prime [2, 3, 73, 44006177] ⟨57824116579, 2, [(2, 1), (3, 2), (73, 1), (44006177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_73
    · exact prime_44006177
  · decide +kernel

theorem prime_58076869489 : Nat.Prime 58076869489 := by
  apply nodeValid_prime [2, 3, 11, 29, 499, 691] ⟨58076869489, 13, [(2, 4), (3, 1), (11, 2), (29, 1), (499, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_499
    · exact prime_691
  · decide +kernel

theorem prime_72201304717 : Nat.Prime 72201304717 := by
  apply nodeValid_prime [2, 3, 181, 241, 137933] ⟨72201304717, 2, [(2, 2), (3, 1), (181, 1), (241, 1), (137933, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_181
    · exact prime_241
    · exact prime_137933
  · decide +kernel

theorem prime_79282056859 : Nat.Prime 79282056859 := by
  apply nodeValid_prime [2, 3, 397, 33283819] ⟨79282056859, 14, [(2, 1), (3, 1), (397, 1), (33283819, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_397
    · exact prime_33283819
  · decide +kernel

theorem prime_126084885203 : Nat.Prime 126084885203 := by
  apply nodeValid_prime [2, 219433, 287297] ⟨126084885203, 2, [(2, 1), (219433, 1), (287297, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_219433
    · exact prime_287297
  · decide +kernel

theorem prime_144245048999 : Nat.Prime 144245048999 := by
  apply nodeValid_prime [2, 701, 102885199] ⟨144245048999, 7, [(2, 1), (701, 1), (102885199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_701
    · exact prime_102885199
  · decide +kernel

theorem prime_173283131383 : Nat.Prime 173283131383 := by
  apply nodeValid_prime [2, 3, 28880521897] ⟨173283131383, 3, [(2, 1), (3, 1), (28880521897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_28880521897
  · decide +kernel

theorem prime_220170072371 : Nat.Prime 220170072371 := by
  apply nodeValid_prime [2, 5, 3163, 6960799] ⟨220170072371, 2, [(2, 1), (5, 1), (3163, 1), (6960799, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3163
    · exact prime_6960799
  · decide +kernel

theorem prime_1729051232123 : Nat.Prime 1729051232123 := by
  apply nodeValid_prime [2, 577, 1498311293] ⟨1729051232123, 2, [(2, 1), (577, 1), (1498311293, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_577
    · exact prime_1498311293
  · decide +kernel

theorem prime_1729051234511 : Nat.Prime 1729051234511 := by
  apply nodeValid_prime [2, 5, 108401, 1595051] ⟨1729051234511, 17, [(2, 1), (5, 1), (108401, 1), (1595051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_108401
    · exact prime_1595051
  · decide +kernel

theorem prime_1729051238891 : Nat.Prime 1729051238891 := by
  apply nodeValid_prime [2, 5, 89, 2731, 711371] ⟨1729051238891, 2, [(2, 1), (5, 1), (89, 1), (2731, 1), (711371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_89
    · exact prime_2731
    · exact prime_711371
  · decide +kernel

theorem prime_1730940587989 : Nat.Prime 1730940587989 := by
  apply nodeValid_prime [2, 3, 144245048999] ⟨1730940587989, 2, [(2, 2), (3, 1), (144245048999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_144245048999
  · decide +kernel

theorem prime_1730940594973 : Nat.Prime 1730940594973 := by
  apply nodeValid_prime [2, 3, 41, 3518171941] ⟨1730940594973, 5, [(2, 2), (3, 1), (41, 1), (3518171941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_3518171941
  · decide +kernel

theorem prime_1730940595729 : Nat.Prime 1730940595729 := by
  apply nodeValid_prime [2, 3, 191, 1301, 145121] ⟨1730940595729, 13, [(2, 4), (3, 1), (191, 1), (1301, 1), (145121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_191
    · exact prime_1301
    · exact prime_145121
  · decide +kernel

theorem prime_1732831313209 : Nat.Prime 1732831313209 := by
  apply nodeValid_prime [2, 3, 72201304717] ⟨1732831313209, 7, [(2, 3), (3, 1), (72201304717, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_72201304717
  · decide +kernel

theorem prime_1732831313831 : Nat.Prime 1732831313831 := by
  apply nodeValid_prime [2, 5, 173283131383] ⟨1732831313831, 7, [(2, 1), (5, 1), (173283131383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_173283131383
  · decide +kernel

theorem prime_1732831335773 : Nat.Prime 1732831335773 := by
  apply nodeValid_prime [2, 3593, 120569951] ⟨1732831335773, 2, [(2, 2), (3593, 1), (120569951, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3593
    · exact prime_120569951
  · decide +kernel

theorem prime_1734723479809 : Nat.Prime 1734723479809 := by
  apply nodeValid_prime [2, 3, 11, 131, 522497] ⟨1734723479809, 7, [(2, 8), (3, 2), (11, 1), (131, 1), (522497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_131
    · exact prime_522497
  · decide +kernel

theorem prime_1734723496963 : Nat.Prime 1734723496963 := by
  apply nodeValid_prime [2, 3, 79, 139, 2925463] ⟨1734723496963, 2, [(2, 1), (3, 3), (79, 1), (139, 1), (2925463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_79
    · exact prime_139
    · exact prime_2925463
  · decide +kernel

theorem prime_1734723497371 : Nat.Prime 1734723497371 := by
  apply nodeValid_prime [2, 3, 5, 57824116579] ⟨1734723497371, 7, [(2, 1), (3, 1), (5, 1), (57824116579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_57824116579
  · decide +kernel

theorem prime_1736617029523 : Nat.Prime 1736617029523 := by
  apply nodeValid_prime [2, 3, 71, 4076565797] ⟨1736617029523, 5, [(2, 1), (3, 1), (71, 1), (4076565797, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_71
    · exact prime_4076565797
  · decide +kernel

theorem prime_1736617033007 : Nat.Prime 1736617033007 := by
  apply nodeValid_prime [2, 17, 19, 5581, 481681] ⟨1736617033007, 5, [(2, 1), (17, 1), (19, 1), (5581, 1), (481681, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_5581
    · exact prime_481681
  · decide +kernel

theorem prime_1736617033829 : Nat.Prime 1736617033829 := by
  apply nodeValid_prime [2, 73, 919, 6471511] ⟨1736617033829, 2, [(2, 2), (73, 1), (919, 1), (6471511, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_919
    · exact prime_6471511
  · decide +kernel

theorem prime_1738511974679 : Nat.Prime 1738511974679 := by
  apply nodeValid_prime [2, 29, 1493, 20076587] ⟨1738511974679, 7, [(2, 1), (29, 1), (1493, 1), (20076587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_1493
    · exact prime_20076587
  · decide +kernel

theorem prime_1738511974943 : Nat.Prime 1738511974943 := by
  apply nodeValid_prime [2, 37783, 23006537] ⟨1738511974943, 5, [(2, 1), (37783, 1), (23006537, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37783
    · exact prime_23006537
  · decide +kernel

theorem prime_1738511979689 : Nat.Prime 1738511979689 := by
  apply nodeValid_prime [2, 11, 743, 26589257] ⟨1738511979689, 3, [(2, 3), (11, 1), (743, 1), (26589257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_743
    · exact prime_26589257
  · decide +kernel

theorem prime_1740408334079 : Nat.Prime 1740408334079 := by
  apply nodeValid_prime [2, 41, 373, 56902123] ⟨1740408334079, 7, [(2, 1), (41, 1), (373, 1), (56902123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_373
    · exact prime_56902123
  · decide +kernel

theorem prime_1740408418429 : Nat.Prime 1740408418429 := by
  apply nodeValid_prime [2, 3, 23, 61, 311, 332393] ⟨1740408418429, 2, [(2, 2), (3, 1), (23, 1), (61, 1), (311, 1), (332393, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_61
    · exact prime_311
    · exact prime_332393
  · decide +kernel

theorem prime_1740408418663 : Nat.Prime 1740408418663 := by
  apply nodeValid_prime [2, 3, 1439, 1453, 138731] ⟨1740408418663, 3, [(2, 1), (3, 1), (1439, 1), (1453, 1), (138731, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1439
    · exact prime_1453
    · exact prime_138731
  · decide +kernel

theorem prime_1742306082653 : Nat.Prime 1742306082653 := by
  apply nodeValid_prime [2, 199, 2188826737] ⟨1742306082653, 2, [(2, 2), (199, 1), (2188826737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_199
    · exact prime_2188826737
  · decide +kernel

theorem prime_1742306083849 : Nat.Prime 1742306083849 := by
  apply nodeValid_prime [2, 3, 11, 43, 1789, 28597] ⟨1742306083849, 13, [(2, 3), (3, 2), (11, 1), (43, 1), (1789, 1), (28597, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_43
    · exact prime_1789
    · exact prime_28597
  · decide +kernel

theorem prime_1742306084671 : Nat.Prime 1742306084671 := by
  apply nodeValid_prime [2, 3, 5, 58076869489] ⟨1742306084671, 12, [(2, 1), (3, 1), (5, 1), (58076869489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_58076869489
  · decide +kernel

theorem prime_1744205230597 : Nat.Prime 1744205230597 := by
  apply nodeValid_prime [2, 3, 37, 106172707] ⟨1744205230597, 5, [(2, 2), (3, 1), (37, 2), (106172707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_106172707
  · decide +kernel

theorem prime_1744205250899 : Nat.Prime 1744205250899 := by
  apply nodeValid_prime [2, 11, 79282056859] ⟨1744205250899, 2, [(2, 1), (11, 1), (79282056859, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_79282056859
  · decide +kernel

theorem prime_1744205251121 : Nat.Prime 1744205251121 := by
  apply nodeValid_prime [2, 5, 31, 53, 13269973] ⟨1744205251121, 3, [(2, 4), (5, 1), (31, 1), (53, 1), (13269973, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
    · exact prime_53
    · exact prime_13269973
  · decide +kernel

theorem prime_1746105768427 : Nat.Prime 1746105768427 := by
  apply nodeValid_prime [2, 3, 197, 1477246843] ⟨1746105768427, 2, [(2, 1), (3, 1), (197, 1), (1477246843, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_197
    · exact prime_1477246843
  · decide +kernel

theorem prime_1746105770221 : Nat.Prime 1746105770221 := by
  apply nodeValid_prime [2, 3, 5, 7, 4157394691] ⟨1746105770221, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (4157394691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_4157394691
  · decide +kernel

theorem prime_1746105771643 : Nat.Prime 1746105771643 := by
  apply nodeValid_prime [2, 3, 2347, 123995581] ⟨1746105771643, 2, [(2, 1), (3, 1), (2347, 1), (123995581, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2347
    · exact prime_123995581
  · decide +kernel

theorem prime_1748007704567 : Nat.Prime 1748007704567 := by
  apply nodeValid_prime [2, 1063, 822204941] ⟨1748007704567, 5, [(2, 1), (1063, 1), (822204941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1063
    · exact prime_822204941
  · decide +kernel

theorem prime_1748007800117 : Nat.Prime 1748007800117 := by
  apply nodeValid_prime [2, 6991, 62509219] ⟨1748007800117, 2, [(2, 2), (6991, 1), (62509219, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_6991
    · exact prime_62509219
  · decide +kernel

theorem prime_1748007802327 : Nat.Prime 1748007802327 := by
  apply nodeValid_prime [2, 3, 311, 936767311] ⟨1748007802327, 3, [(2, 1), (3, 1), (311, 1), (936767311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_311
    · exact prime_936767311
  · decide +kernel

theorem prime_1749911045083 : Nat.Prime 1749911045083 := by
  apply nodeValid_prime [2, 3, 179, 1629339893] ⟨1749911045083, 3, [(2, 1), (3, 1), (179, 1), (1629339893, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_1629339893
  · decide +kernel

theorem prime_1749911068637 : Nat.Prime 1749911068637 := by
  apply nodeValid_prime [2, 41213, 10615043] ⟨1749911068637, 2, [(2, 2), (41213, 1), (10615043, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41213
    · exact prime_10615043
  · decide +kernel

theorem prime_1749911069213 : Nat.Prime 1749911069213 := by
  apply nodeValid_prime [2, 79, 70097383] ⟨1749911069213, 2, [(2, 2), (79, 2), (70097383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_79
    · exact prime_70097383
  · decide +kernel

theorem prime_1751815743019 : Nat.Prime 1751815743019 := by
  apply nodeValid_prime [2, 3, 11, 113, 21353711] ⟨1751815743019, 3, [(2, 1), (3, 1), (11, 2), (113, 1), (21353711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_113
    · exact prime_21353711
  · decide +kernel

theorem prime_1751815743071 : Nat.Prime 1751815743071 := by
  apply nodeValid_prime [2, 5, 61, 71, 523, 77339] ⟨1751815743071, 7, [(2, 1), (5, 1), (61, 1), (71, 1), (523, 1), (77339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_61
    · exact prime_71
    · exact prime_523
    · exact prime_77339
  · decide +kernel

theorem prime_1751815787947 : Nat.Prime 1751815787947 := by
  apply nodeValid_prime [2, 3, 7, 907, 45986659] ⟨1751815787947, 2, [(2, 1), (3, 1), (7, 1), (907, 1), (45986659, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_907
    · exact prime_45986659
  · decide +kernel

theorem prime_1753721866679 : Nat.Prime 1753721866679 := by
  apply nodeValid_prime [2, 61, 67, 349, 614753] ⟨1753721866679, 17, [(2, 1), (61, 1), (67, 1), (349, 1), (614753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_67
    · exact prime_349
    · exact prime_614753
  · decide +kernel

theorem prime_1753721867047 : Nat.Prime 1753721867047 := by
  apply nodeValid_prime [2, 3, 122777, 2380633] ⟨1753721867047, 3, [(2, 1), (3, 1), (122777, 1), (2380633, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_122777
    · exact prime_2380633
  · decide +kernel

theorem prime_1753721935759 : Nat.Prime 1753721935759 := by
  apply nodeValid_prime [2, 3, 13, 27733, 270239] ⟨1753721935759, 3, [(2, 1), (3, 2), (13, 1), (27733, 1), (270239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_27733
    · exact prime_270239
  · decide +kernel

theorem prime_1755629491373 : Nat.Prime 1755629491373 := by
  apply nodeValid_prime [2, 479, 916299317] ⟨1755629491373, 2, [(2, 2), (479, 1), (916299317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_479
    · exact prime_916299317
  · decide +kernel

theorem prime_1755629503619 : Nat.Prime 1755629503619 := by
  apply nodeValid_prime [2, 19, 46200776411] ⟨1755629503619, 2, [(2, 1), (19, 1), (46200776411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_46200776411
  · decide +kernel

theorem prime_1755629506073 : Nat.Prime 1755629506073 := by
  apply nodeValid_prime [2, 13, 233, 311, 232961] ⟨1755629506073, 3, [(2, 3), (13, 1), (233, 1), (311, 1), (232961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_233
    · exact prime_311
    · exact prime_232961
  · decide +kernel

theorem prime_1757538447947 : Nat.Prime 1757538447947 := by
  apply nodeValid_prime [2, 1031, 5897, 144539] ⟨1757538447947, 2, [(2, 1), (1031, 1), (5897, 1), (144539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1031
    · exact prime_5897
    · exact prime_144539
  · decide +kernel

theorem prime_1757538476971 : Nat.Prime 1757538476971 := by
  apply nodeValid_prime [2, 3, 5, 23, 401, 6352013] ⟨1757538476971, 10, [(2, 1), (3, 1), (5, 1), (23, 1), (401, 1), (6352013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_401
    · exact prime_6352013
  · decide +kernel

theorem prime_1757538477503 : Nat.Prime 1757538477503 := by
  apply nodeValid_prime [2, 113, 2309, 3368003] ⟨1757538477503, 5, [(2, 1), (113, 1), (2309, 1), (3368003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_113
    · exact prime_2309
    · exact prime_3368003
  · decide +kernel

theorem prime_1759448782717 : Nat.Prime 1759448782717 := by
  apply nodeValid_prime [2, 3, 353, 415356181] ⟨1759448782717, 2, [(2, 2), (3, 1), (353, 1), (415356181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_353
    · exact prime_415356181
  · decide +kernel

theorem prime_1759448783371 : Nat.Prime 1759448783371 := by
  apply nodeValid_prime [2, 3, 5, 23, 2549925773] ⟨1759448783371, 2, [(2, 1), (3, 1), (5, 1), (23, 1), (2549925773, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_2549925773
  · decide +kernel

theorem prime_1759448820979 : Nat.Prime 1759448820979 := by
  apply nodeValid_prime [2, 3, 83, 1177676587] ⟨1759448820979, 2, [(2, 1), (3, 2), (83, 1), (1177676587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
    · exact prime_1177676587
  · decide +kernel

theorem prime_1761360578333 : Nat.Prime 1761360578333 := by
  apply nodeValid_prime [2, 31, 14204520793] ⟨1761360578333, 2, [(2, 2), (31, 1), (14204520793, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_14204520793
  · decide +kernel

theorem prime_1761360578969 : Nat.Prime 1761360578969 := by
  apply nodeValid_prime [2, 220170072371] ⟨1761360578969, 3, [(2, 3), (220170072371, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_220170072371
  · decide +kernel

theorem prime_1761360594163 : Nat.Prime 1761360594163 := by
  apply nodeValid_prime [2, 3, 13, 277, 81521827] ⟨1761360594163, 2, [(2, 1), (3, 1), (13, 1), (277, 1), (81521827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_277
    · exact prime_81521827
  · decide +kernel

theorem prime_1763273771491 : Nat.Prime 1763273771491 := by
  apply nodeValid_prime [2, 3, 5, 7, 11, 19, 103, 55721] ⟨1763273771491, 13, [(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (19, 1), (103, 1), (55721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_103
    · exact prime_55721
  · decide +kernel

theorem prime_1763273772553 : Nat.Prime 1763273772553 := by
  apply nodeValid_prime [2, 3, 107, 151, 4547239] ⟨1763273772553, 5, [(2, 3), (3, 1), (107, 1), (151, 1), (4547239, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_151
    · exact prime_4547239
  · decide +kernel

theorem prime_1763273772943 : Nat.Prime 1763273772943 := by
  apply nodeValid_prime [2, 3, 11, 26716269287] ⟨1763273772943, 5, [(2, 1), (3, 1), (11, 1), (26716269287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_26716269287
  · decide +kernel

theorem prime_1765188359549 : Nat.Prime 1765188359549 := by
  apply nodeValid_prime [2, 59, 7479611693] ⟨1765188359549, 2, [(2, 2), (59, 1), (7479611693, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_59
    · exact prime_7479611693
  · decide +kernel

theorem prime_1765188392489 : Nat.Prime 1765188392489 := by
  apply nodeValid_prime [2, 31, 7117695131] ⟨1765188392489, 3, [(2, 3), (31, 1), (7117695131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_7117695131
  · decide +kernel

theorem prime_1765188392843 : Nat.Prime 1765188392843 := by
  apply nodeValid_prime [2, 7, 126084885203] ⟨1765188392843, 2, [(2, 1), (7, 1), (126084885203, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_126084885203
  · decide +kernel

theorem prime_1767104348881 : Nat.Prime 1767104348881 := by
  apply nodeValid_prime [2, 3, 5, 13, 17, 29, 67579] ⟨1767104348881, 31, [(2, 4), (3, 1), (5, 1), (13, 1), (17, 2), (29, 1), (67579, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_29
    · exact prime_67579
  · decide +kernel

theorem prime_1767104348899 : Nat.Prime 1767104348899 := by
  apply nodeValid_prime [2, 3, 7, 128563, 327263] ⟨1767104348899, 2, [(2, 1), (3, 1), (7, 1), (128563, 1), (327263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_128563
    · exact prime_327263
  · decide +kernel

theorem prime_1767104364497 : Nat.Prime 1767104364497 := by
  apply nodeValid_prime [2, 97, 1138598173] ⟨1767104364497, 3, [(2, 4), (97, 1), (1138598173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_97
    · exact prime_1138598173
  · decide +kernel

theorem prime_1769021770597 : Nat.Prime 1769021770597 := by
  apply nodeValid_prime [2, 3, 223, 359, 587, 3137] ⟨1769021770597, 2, [(2, 2), (3, 1), (223, 1), (359, 1), (587, 1), (3137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_223
    · exact prime_359
    · exact prime_587
    · exact prime_3137
  · decide +kernel

theorem prime_1769021770921 : Nat.Prime 1769021770921 := by
  apply nodeValid_prime [2, 3, 5, 23, 941, 681137] ⟨1769021770921, 17, [(2, 3), (3, 1), (5, 1), (23, 1), (941, 1), (681137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
    · exact prime_941
    · exact prime_681137
  · decide +kernel

theorem prime_1769021780401 : Nat.Prime 1769021780401 := by
  apply nodeValid_prime [2, 3, 5, 7, 23399759] ⟨1769021780401, 11, [(2, 4), (3, 3), (5, 2), (7, 1), (23399759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23399759
  · decide +kernel

theorem prime_1770940551811 : Nat.Prime 1770940551811 := by
  apply nodeValid_prime [2, 3, 5, 12569, 4696583] ⟨1770940551811, 3, [(2, 1), (3, 1), (5, 1), (12569, 1), (4696583, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_12569
    · exact prime_4696583
  · decide +kernel

theorem prime_1770940556023 : Nat.Prime 1770940556023 := by
  apply nodeValid_prime [2, 3, 11, 89227, 300721] ⟨1770940556023, 3, [(2, 1), (3, 1), (11, 1), (89227, 1), (300721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_89227
    · exact prime_300721
  · decide +kernel

theorem prime_1770940612057 : Nat.Prime 1770940612057 := by
  apply nodeValid_prime [2, 3, 7, 11, 977, 140123] ⟨1770940612057, 13, [(2, 3), (3, 1), (7, 2), (11, 1), (977, 1), (140123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_977
    · exact prime_140123
  · decide +kernel

theorem prime_1772860847851 : Nat.Prime 1772860847851 := by
  apply nodeValid_prime [2, 3, 5, 37, 4261, 24989] ⟨1772860847851, 3, [(2, 1), (3, 2), (5, 2), (37, 1), (4261, 1), (24989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
    · exact prime_4261
    · exact prime_24989
  · decide +kernel

theorem prime_1772860857217 : Nat.Prime 1772860857217 := by
  apply nodeValid_prime [2, 3, 4616825149] ⟨1772860857217, 5, [(2, 7), (3, 1), (4616825149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4616825149
  · decide +kernel

theorem prime_1772860857541 : Nat.Prime 1772860857541 := by
  apply nodeValid_prime [2, 3, 5, 29547680959] ⟨1772860857541, 6, [(2, 2), (3, 1), (5, 1), (29547680959, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29547680959
  · decide +kernel

theorem prime_1774782496603 : Nat.Prime 1774782496603 := by
  apply nodeValid_prime [2, 3, 23, 4286914243] ⟨1774782496603, 3, [(2, 1), (3, 2), (23, 1), (4286914243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_4286914243
  · decide +kernel

theorem prime_1774782497101 : Nat.Prime 1774782497101 := by
  apply nodeValid_prime [2, 3, 5, 5915941657] ⟨1774782497101, 2, [(2, 2), (3, 1), (5, 2), (5915941657, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5915941657
  · decide +kernel

theorem prime_1774782497617 : Nat.Prime 1774782497617 := by
  apply nodeValid_prime [2, 3, 17, 859, 2531989] ⟨1774782497617, 7, [(2, 4), (3, 1), (17, 1), (859, 1), (2531989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_859
    · exact prime_2531989
  · decide +kernel

end Sude.Lucas.Generated
