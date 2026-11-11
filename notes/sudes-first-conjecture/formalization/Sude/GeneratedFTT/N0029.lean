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
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0022
import Sude.GeneratedFTT.N0026
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2939 : Nat.Prime 2939 := by
  apply nodeValid_prime [2, 13, 113] ⟨2939, 2, [(2, 1), (13, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_113
  · decide +kernel

theorem prime_2963 : Nat.Prime 2963 := by
  apply nodeValid_prime [2, 1481] ⟨2963, 2, [(2, 1), (1481, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1481
  · decide +kernel

theorem prime_3121 : Nat.Prime 3121 := by
  apply nodeValid_prime [2, 3, 5, 13] ⟨3121, 7, [(2, 4), (3, 1), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_3203 : Nat.Prime 3203 := by
  apply nodeValid_prime [2, 1601] ⟨3203, 2, [(2, 1), (1601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1601
  · decide +kernel

theorem prime_3529 : Nat.Prime 3529 := by
  apply nodeValid_prime [2, 3, 7] ⟨3529, 17, [(2, 3), (3, 2), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_4079 : Nat.Prime 4079 := by
  apply nodeValid_prime [2, 2039] ⟨4079, 11, [(2, 1), (2039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2039
  · decide +kernel

theorem prime_4111 : Nat.Prime 4111 := by
  apply nodeValid_prime [2, 3, 5, 137] ⟨4111, 12, [(2, 1), (3, 1), (5, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_137
  · decide +kernel

theorem prime_4229 : Nat.Prime 4229 := by
  apply nodeValid_prime [2, 7, 151] ⟨4229, 2, [(2, 2), (7, 1), (151, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_151
  · decide +kernel

theorem prime_4421 : Nat.Prime 4421 := by
  apply nodeValid_prime [2, 5, 13, 17] ⟨4421, 3, [(2, 2), (5, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_5569 : Nat.Prime 5569 := by
  apply nodeValid_prime [2, 3, 29] ⟨5569, 13, [(2, 6), (3, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_6491 : Nat.Prime 6491 := by
  apply nodeValid_prime [2, 5, 11, 59] ⟨6491, 2, [(2, 1), (5, 1), (11, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_59
  · decide +kernel

theorem prime_6703 : Nat.Prime 6703 := by
  apply nodeValid_prime [2, 3, 1117] ⟨6703, 5, [(2, 1), (3, 1), (1117, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1117
  · decide +kernel

theorem prime_7207 : Nat.Prime 7207 := by
  apply nodeValid_prime [2, 3, 1201] ⟨7207, 3, [(2, 1), (3, 1), (1201, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1201
  · decide +kernel

theorem prime_7717 : Nat.Prime 7717 := by
  apply nodeValid_prime [2, 3, 643] ⟨7717, 2, [(2, 2), (3, 1), (643, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_643
  · decide +kernel

theorem prime_9601 : Nat.Prime 9601 := by
  apply nodeValid_prime [2, 3, 5] ⟨9601, 13, [(2, 7), (3, 1), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_11087 : Nat.Prime 11087 := by
  apply nodeValid_prime [2, 23, 241] ⟨11087, 5, [(2, 1), (23, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_241
  · decide +kernel

theorem prime_13567 : Nat.Prime 13567 := by
  apply nodeValid_prime [2, 3, 7, 17, 19] ⟨13567, 3, [(2, 1), (3, 1), (7, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_14173 : Nat.Prime 14173 := by
  apply nodeValid_prime [2, 3, 1181] ⟨14173, 2, [(2, 2), (3, 1), (1181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1181
  · decide +kernel

theorem prime_14323 : Nat.Prime 14323 := by
  apply nodeValid_prime [2, 3, 7, 11, 31] ⟨14323, 5, [(2, 1), (3, 1), (7, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_15013 : Nat.Prime 15013 := by
  apply nodeValid_prime [2, 3, 139] ⟨15013, 2, [(2, 2), (3, 3), (139, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_139
  · decide +kernel

theorem prime_15647 : Nat.Prime 15647 := by
  apply nodeValid_prime [2, 7823] ⟨15647, 5, [(2, 1), (7823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7823
  · decide +kernel

theorem prime_17977 : Nat.Prime 17977 := by
  apply nodeValid_prime [2, 3, 7, 107] ⟨17977, 5, [(2, 3), (3, 1), (7, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_107
  · decide +kernel

theorem prime_19037 : Nat.Prime 19037 := by
  apply nodeValid_prime [2, 4759] ⟨19037, 2, [(2, 2), (4759, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4759
  · decide +kernel

theorem prime_19417 : Nat.Prime 19417 := by
  apply nodeValid_prime [2, 3, 809] ⟨19417, 5, [(2, 3), (3, 1), (809, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_809
  · decide +kernel

theorem prime_19699 : Nat.Prime 19699 := by
  apply nodeValid_prime [2, 3, 7, 67] ⟨19699, 7, [(2, 1), (3, 1), (7, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_67
  · decide +kernel

theorem prime_21107 : Nat.Prime 21107 := by
  apply nodeValid_prime [2, 61, 173] ⟨21107, 2, [(2, 1), (61, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_173
  · decide +kernel

theorem prime_21961 : Nat.Prime 21961 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨21961, 17, [(2, 3), (3, 2), (5, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_22277 : Nat.Prime 22277 := by
  apply nodeValid_prime [2, 5569] ⟨22277, 2, [(2, 2), (5569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5569
  · decide +kernel

theorem prime_25261 : Nat.Prime 25261 := by
  apply nodeValid_prime [2, 3, 5, 421] ⟨25261, 7, [(2, 2), (3, 1), (5, 1), (421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_421
  · decide +kernel

theorem prime_26497 : Nat.Prime 26497 := by
  apply nodeValid_prime [2, 3, 23] ⟨26497, 5, [(2, 7), (3, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_27689 : Nat.Prime 27689 := by
  apply nodeValid_prime [2, 3461] ⟨27689, 3, [(2, 3), (3461, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3461
  · decide +kernel

theorem prime_28409 : Nat.Prime 28409 := by
  apply nodeValid_prime [2, 53, 67] ⟨28409, 3, [(2, 3), (53, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_67
  · decide +kernel

theorem prime_29429 : Nat.Prime 29429 := by
  apply nodeValid_prime [2, 7, 1051] ⟨29429, 2, [(2, 2), (7, 1), (1051, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1051
  · decide +kernel

theorem prime_29641 : Nat.Prime 29641 := by
  apply nodeValid_prime [2, 3, 5, 13, 19] ⟨29641, 7, [(2, 3), (3, 1), (5, 1), (13, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_19
  · decide +kernel

theorem prime_32189 : Nat.Prime 32189 := by
  apply nodeValid_prime [2, 13, 619] ⟨32189, 2, [(2, 2), (13, 1), (619, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_619
  · decide +kernel

theorem prime_36523 : Nat.Prime 36523 := by
  apply nodeValid_prime [2, 3, 2029] ⟨36523, 2, [(2, 1), (3, 2), (2029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2029
  · decide +kernel

theorem prime_37273 : Nat.Prime 37273 := by
  apply nodeValid_prime [2, 3, 1553] ⟨37273, 5, [(2, 3), (3, 1), (1553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1553
  · decide +kernel

theorem prime_39181 : Nat.Prime 39181 := by
  apply nodeValid_prime [2, 3, 5, 653] ⟨39181, 6, [(2, 2), (3, 1), (5, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_653
  · decide +kernel

theorem prime_40039 : Nat.Prime 40039 := by
  apply nodeValid_prime [2, 3, 6673] ⟨40039, 6, [(2, 1), (3, 1), (6673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6673
  · decide +kernel

theorem prime_40429 : Nat.Prime 40429 := by
  apply nodeValid_prime [2, 3, 1123] ⟨40429, 14, [(2, 2), (3, 2), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1123
  · decide +kernel

theorem prime_43159 : Nat.Prime 43159 := by
  apply nodeValid_prime [2, 3, 7193] ⟨43159, 3, [(2, 1), (3, 1), (7193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7193
  · decide +kernel

theorem prime_44497 : Nat.Prime 44497 := by
  apply nodeValid_prime [2, 3, 103] ⟨44497, 5, [(2, 4), (3, 3), (103, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
  · decide +kernel

theorem prime_52639 : Nat.Prime 52639 := by
  apply nodeValid_prime [2, 3, 31, 283] ⟨52639, 3, [(2, 1), (3, 1), (31, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_283
  · decide +kernel

theorem prime_55333 : Nat.Prime 55333 := by
  apply nodeValid_prime [2, 3, 29, 53] ⟨55333, 6, [(2, 2), (3, 2), (29, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_53
  · decide +kernel

theorem prime_56503 : Nat.Prime 56503 := by
  apply nodeValid_prime [2, 3, 43, 73] ⟨56503, 3, [(2, 1), (3, 2), (43, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_73
  · decide +kernel

theorem prime_56629 : Nat.Prime 56629 := by
  apply nodeValid_prime [2, 3, 11, 13] ⟨56629, 2, [(2, 2), (3, 2), (11, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_66337 : Nat.Prime 66337 := by
  apply nodeValid_prime [2, 3, 691] ⟨66337, 5, [(2, 5), (3, 1), (691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_691
  · decide +kernel

theorem prime_74747 : Nat.Prime 74747 := by
  apply nodeValid_prime [2, 7, 19, 281] ⟨74747, 2, [(2, 1), (7, 1), (19, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_19
    · exact prime_281
  · decide +kernel

theorem prime_126341 : Nat.Prime 126341 := by
  apply nodeValid_prime [2, 5, 6317] ⟨126341, 3, [(2, 2), (5, 1), (6317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_6317
  · decide +kernel

theorem prime_128201 : Nat.Prime 128201 := by
  apply nodeValid_prime [2, 5, 641] ⟨128201, 3, [(2, 3), (5, 2), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_641
  · decide +kernel

theorem prime_139721 : Nat.Prime 139721 := by
  apply nodeValid_prime [2, 5, 7, 499] ⟨139721, 15, [(2, 3), (5, 1), (7, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_499
  · decide +kernel

theorem prime_146977 : Nat.Prime 146977 := by
  apply nodeValid_prime [2, 3, 1531] ⟨146977, 5, [(2, 5), (3, 1), (1531, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1531
  · decide +kernel

theorem prime_147997 : Nat.Prime 147997 := by
  apply nodeValid_prime [2, 3, 4111] ⟨147997, 2, [(2, 2), (3, 2), (4111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4111
  · decide +kernel

theorem prime_155003 : Nat.Prime 155003 := by
  apply nodeValid_prime [2, 19, 4079] ⟨155003, 2, [(2, 1), (19, 1), (4079, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_4079
  · decide +kernel

theorem prime_165983 : Nat.Prime 165983 := by
  apply nodeValid_prime [2, 37, 2243] ⟨165983, 5, [(2, 1), (37, 1), (2243, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_2243
  · decide +kernel

theorem prime_167449 : Nat.Prime 167449 := by
  apply nodeValid_prime [2, 3, 6977] ⟨167449, 11, [(2, 3), (3, 1), (6977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6977
  · decide +kernel

theorem prime_189361 : Nat.Prime 189361 := by
  apply nodeValid_prime [2, 3, 5, 263] ⟨189361, 11, [(2, 4), (3, 2), (5, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_211153 : Nat.Prime 211153 := by
  apply nodeValid_prime [2, 3, 53, 83] ⟨211153, 5, [(2, 4), (3, 1), (53, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_53
    · exact prime_83
  · decide +kernel

theorem prime_224153 : Nat.Prime 224153 := by
  apply nodeValid_prime [2, 28019] ⟨224153, 3, [(2, 3), (28019, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_28019
  · decide +kernel

theorem prime_236573 : Nat.Prime 236573 := by
  apply nodeValid_prime [2, 7, 17, 71] ⟨236573, 2, [(2, 2), (7, 2), (17, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_71
  · decide +kernel

theorem prime_261347 : Nat.Prime 261347 := by
  apply nodeValid_prime [2, 149, 877] ⟨261347, 2, [(2, 1), (149, 1), (877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_877
  · decide +kernel

theorem prime_294227 : Nat.Prime 294227 := by
  apply nodeValid_prime [2, 131, 1123] ⟨294227, 2, [(2, 1), (131, 1), (1123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_131
    · exact prime_1123
  · decide +kernel

theorem prime_400391 : Nat.Prime 400391 := by
  apply nodeValid_prime [2, 5, 40039] ⟨400391, 17, [(2, 1), (5, 1), (40039, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_40039
  · decide +kernel

theorem prime_446983 : Nat.Prime 446983 := by
  apply nodeValid_prime [2, 3, 23, 41, 79] ⟨446983, 3, [(2, 1), (3, 1), (23, 1), (41, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_41
    · exact prime_79
  · decide +kernel

theorem prime_473147 : Nat.Prime 473147 := by
  apply nodeValid_prime [2, 236573] ⟨473147, 2, [(2, 1), (236573, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_236573
  · decide +kernel

theorem prime_577097 : Nat.Prime 577097 := by
  apply nodeValid_prime [2, 13, 31, 179] ⟨577097, 3, [(2, 3), (13, 1), (31, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_179
  · decide +kernel

theorem prime_633667 : Nat.Prime 633667 := by
  apply nodeValid_prime [2, 3, 11, 9601] ⟨633667, 2, [(2, 1), (3, 1), (11, 1), (9601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_9601
  · decide +kernel

theorem prime_696263 : Nat.Prime 696263 := by
  apply nodeValid_prime [2, 7, 41, 1213] ⟨696263, 5, [(2, 1), (7, 1), (41, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_41
    · exact prime_1213
  · decide +kernel

theorem prime_798697 : Nat.Prime 798697 := by
  apply nodeValid_prime [2, 3, 11093] ⟨798697, 15, [(2, 3), (3, 2), (11093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11093
  · decide +kernel

theorem prime_861877 : Nat.Prime 861877 := by
  apply nodeValid_prime [2, 3, 89, 269] ⟨861877, 6, [(2, 2), (3, 2), (89, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_269
  · decide +kernel

theorem prime_884803 : Nat.Prime 884803 := by
  apply nodeValid_prime [2, 3, 31, 67, 71] ⟨884803, 3, [(2, 1), (3, 1), (31, 1), (67, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_67
    · exact prime_71
  · decide +kernel

theorem prime_889439 : Nat.Prime 889439 := by
  apply nodeValid_prime [2, 11, 40429] ⟨889439, 11, [(2, 1), (11, 1), (40429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_40429
  · decide +kernel

theorem prime_1322329 : Nat.Prime 1322329 := by
  apply nodeValid_prime [2, 3, 7, 17, 463] ⟨1322329, 13, [(2, 3), (3, 1), (7, 1), (17, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_463
  · decide +kernel

theorem prime_1331411 : Nat.Prime 1331411 := by
  apply nodeValid_prime [2, 5, 211, 631] ⟨1331411, 2, [(2, 1), (5, 1), (211, 1), (631, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_211
    · exact prime_631
  · decide +kernel

theorem prime_1778879 : Nat.Prime 1778879 := by
  apply nodeValid_prime [2, 889439] ⟨1778879, 7, [(2, 1), (889439, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_889439
  · decide +kernel

theorem prime_2157457 : Nat.Prime 2157457 := by
  apply nodeValid_prime [2, 3, 7, 6421] ⟨2157457, 5, [(2, 4), (3, 1), (7, 1), (6421, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6421
  · decide +kernel

theorem prime_2307967 : Nat.Prime 2307967 := by
  apply nodeValid_prime [2, 3, 109, 3529] ⟨2307967, 3, [(2, 1), (3, 1), (109, 1), (3529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_3529
  · decide +kernel

theorem prime_2764453 : Nat.Prime 2764453 := by
  apply nodeValid_prime [2, 3, 107, 2153] ⟨2764453, 2, [(2, 2), (3, 1), (107, 1), (2153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_2153
  · decide +kernel

theorem prime_3284483 : Nat.Prime 3284483 := by
  apply nodeValid_prime [2, 29, 56629] ⟨3284483, 2, [(2, 1), (29, 1), (56629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_56629
  · decide +kernel

theorem prime_3284867 : Nat.Prime 3284867 := by
  apply nodeValid_prime [2, 13, 126341] ⟨3284867, 2, [(2, 1), (13, 1), (126341, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_126341
  · decide +kernel

theorem prime_3336967 : Nat.Prime 3336967 := by
  apply nodeValid_prime [2, 3, 89, 2083] ⟨3336967, 3, [(2, 1), (3, 2), (89, 1), (2083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_2083
  · decide +kernel

theorem prime_3940091 : Nat.Prime 3940091 := by
  apply nodeValid_prime [2, 5, 7, 11, 17, 43] ⟨3940091, 2, [(2, 1), (5, 1), (7, 2), (11, 1), (17, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_17
    · exact prime_43
  · decide +kernel

theorem prime_4016171 : Nat.Prime 4016171 := by
  apply nodeValid_prime [2, 5, 269, 1493] ⟨4016171, 2, [(2, 1), (5, 1), (269, 1), (1493, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_269
    · exact prime_1493
  · decide +kernel

theorem prime_4471073 : Nat.Prime 4471073 := by
  apply nodeValid_prime [2, 139721] ⟨4471073, 3, [(2, 5), (139721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_139721
  · decide +kernel

theorem prime_5789233 : Nat.Prime 5789233 := by
  apply nodeValid_prime [2, 3, 1489] ⟨5789233, 5, [(2, 4), (3, 5), (1489, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1489
  · decide +kernel

theorem prime_6198691 : Nat.Prime 6198691 := by
  apply nodeValid_prime [2, 3, 5, 206623] ⟨6198691, 10, [(2, 1), (3, 1), (5, 1), (206623, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_206623
  · decide +kernel

theorem prime_8564791 : Nat.Prime 8564791 := by
  apply nodeValid_prime [2, 3, 5, 13, 21961] ⟨8564791, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (21961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_21961
  · decide +kernel

theorem prime_9644909 : Nat.Prime 9644909 := by
  apply nodeValid_prime [2, 7, 13, 26497] ⟨9644909, 2, [(2, 2), (7, 1), (13, 1), (26497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_13
    · exact prime_26497
  · decide +kernel

theorem prime_12340687 : Nat.Prime 12340687 := by
  apply nodeValid_prime [2, 3, 137, 15013] ⟨12340687, 3, [(2, 1), (3, 1), (137, 1), (15013, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
    · exact prime_15013
  · decide +kernel

theorem prime_14267861 : Nat.Prime 14267861 := by
  apply nodeValid_prime [2, 5, 19, 37547] ⟨14267861, 2, [(2, 2), (5, 1), (19, 1), (37547, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_37547
  · decide +kernel

theorem prime_26892529 : Nat.Prime 26892529 := by
  apply nodeValid_prime [2, 3, 13, 71, 607] ⟨26892529, 7, [(2, 4), (3, 1), (13, 1), (71, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_71
    · exact prime_607
  · decide +kernel

theorem prime_36072709 : Nat.Prime 36072709 := by
  apply nodeValid_prime [2, 3, 7, 17, 25261] ⟨36072709, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (25261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_25261
  · decide +kernel

theorem prime_41370097 : Nat.Prime 41370097 := by
  apply nodeValid_prime [2, 3, 861877] ⟨41370097, 7, [(2, 4), (3, 1), (861877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_861877
  · decide +kernel

theorem prime_45116627 : Nat.Prime 45116627 := by
  apply nodeValid_prime [2, 109, 349, 593] ⟨45116627, 2, [(2, 1), (109, 1), (349, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_349
    · exact prime_593
  · decide +kernel

theorem prime_52329007 : Nat.Prime 52329007 := by
  apply nodeValid_prime [2, 3, 1279, 2273] ⟨52329007, 6, [(2, 1), (3, 2), (1279, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1279
    · exact prime_2273
  · decide +kernel

theorem prime_54494269 : Nat.Prime 54494269 := by
  apply nodeValid_prime [2, 3, 23, 347, 569] ⟨54494269, 2, [(2, 2), (3, 1), (23, 1), (347, 1), (569, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_347
    · exact prime_569
  · decide +kernel

theorem prime_56696557 : Nat.Prime 56696557 := by
  apply nodeValid_prime [2, 3, 7, 103, 6553] ⟨56696557, 2, [(2, 2), (3, 1), (7, 1), (103, 1), (6553, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_103
    · exact prime_6553
  · decide +kernel

theorem prime_69250651 : Nat.Prime 69250651 := by
  apply nodeValid_prime [2, 3, 5, 7, 101, 653] ⟨69250651, 12, [(2, 1), (3, 1), (5, 2), (7, 1), (101, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_101
    · exact prime_653
  · decide +kernel

theorem prime_91975339 : Nat.Prime 91975339 := by
  apply nodeValid_prime [2, 3, 7, 13, 17, 367] ⟨91975339, 2, [(2, 1), (3, 4), (7, 1), (13, 1), (17, 1), (367, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_17
    · exact prime_367
  · decide +kernel

theorem prime_103141663 : Nat.Prime 103141663 := by
  apply nodeValid_prime [2, 3, 13, 1322329] ⟨103141663, 6, [(2, 1), (3, 1), (13, 1), (1322329, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1322329
  · decide +kernel

theorem prime_110578121 : Nat.Prime 110578121 := by
  apply nodeValid_prime [2, 5, 2764453] ⟨110578121, 3, [(2, 3), (5, 1), (2764453, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2764453
  · decide +kernel

theorem prime_158784779 : Nat.Prime 158784779 := by
  apply nodeValid_prime [2, 23, 241, 14323] ⟨158784779, 2, [(2, 1), (23, 1), (241, 1), (14323, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_241
    · exact prime_14323
  · decide +kernel

theorem prime_164243351 : Nat.Prime 164243351 := by
  apply nodeValid_prime [2, 5, 3284867] ⟨164243351, 17, [(2, 1), (5, 2), (3284867, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_3284867
  · decide +kernel

theorem prime_369228127 : Nat.Prime 369228127 := by
  apply nodeValid_prime [2, 3, 109, 347, 1627] ⟨369228127, 3, [(2, 1), (3, 1), (109, 1), (347, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_109
    · exact prime_347
    · exact prime_1627
  · decide +kernel

theorem prime_427044089 : Nat.Prime 427044089 := by
  apply nodeValid_prime [2, 1879, 28409] ⟨427044089, 3, [(2, 3), (1879, 1), (28409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1879
    · exact prime_28409
  · decide +kernel

theorem prime_487326089 : Nat.Prime 487326089 := by
  apply nodeValid_prime [2, 367, 165983] ⟨487326089, 3, [(2, 3), (367, 1), (165983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_367
    · exact prime_165983
  · decide +kernel

theorem prime_498520873 : Nat.Prime 498520873 := by
  apply nodeValid_prime [2, 3, 2307967] ⟨498520873, 5, [(2, 3), (3, 3), (2307967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2307967
  · decide +kernel

theorem prime_583969871 : Nat.Prime 583969871 := by
  apply nodeValid_prime [2, 5, 11, 797, 6661] ⟨583969871, 7, [(2, 1), (5, 1), (11, 1), (797, 1), (6661, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_797
    · exact prime_6661
  · decide +kernel

theorem prime_765218473 : Nat.Prime 765218473 := by
  apply nodeValid_prime [2, 3, 151, 211153] ⟨765218473, 5, [(2, 3), (3, 1), (151, 1), (211153, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_151
    · exact prime_211153
  · decide +kernel

theorem prime_884624969 : Nat.Prime 884624969 := by
  apply nodeValid_prime [2, 110578121] ⟨884624969, 3, [(2, 3), (110578121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_110578121
  · decide +kernel

theorem prime_1167939961 : Nat.Prime 1167939961 := by
  apply nodeValid_prime [2, 3, 5, 11, 884803] ⟨1167939961, 14, [(2, 3), (3, 1), (5, 1), (11, 1), (884803, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_884803
  · decide +kernel

theorem prime_1248773059 : Nat.Prime 1248773059 := by
  apply nodeValid_prime [2, 3, 13, 1778879] ⟨1248773059, 2, [(2, 1), (3, 3), (13, 1), (1778879, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_1778879
  · decide +kernel

theorem prime_1409145433 : Nat.Prime 1409145433 := by
  apply nodeValid_prime [2, 3, 43, 163, 8377] ⟨1409145433, 5, [(2, 3), (3, 1), (43, 1), (163, 1), (8377, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_163
    · exact prime_8377
  · decide +kernel

theorem prime_1795328083 : Nat.Prime 1795328083 := by
  apply nodeValid_prime [2, 3, 2311, 43159] ⟨1795328083, 2, [(2, 1), (3, 2), (2311, 1), (43159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2311
    · exact prime_43159
  · decide +kernel

theorem prime_1798606111 : Nat.Prime 1798606111 := by
  apply nodeValid_prime [2, 3, 5, 7, 8564791] ⟨1798606111, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (8564791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_8564791
  · decide +kernel

theorem prime_2281401233 : Nat.Prime 2281401233 := by
  apply nodeValid_prime [2, 11, 29, 446983] ⟨2281401233, 3, [(2, 4), (11, 1), (29, 1), (446983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_29
    · exact prime_446983
  · decide +kernel

theorem prime_2493023437 : Nat.Prime 2493023437 := by
  apply nodeValid_prime [2, 3, 69250651] ⟨2493023437, 5, [(2, 2), (3, 2), (69250651, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_69250651
  · decide +kernel

theorem prime_3405971753 : Nat.Prime 3405971753 := by
  apply nodeValid_prime [2, 1447, 294227] ⟨3405971753, 3, [(2, 3), (1447, 1), (294227, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1447
    · exact prime_294227
  · decide +kernel

theorem prime_6648063067 : Nat.Prime 6648063067 := by
  apply nodeValid_prime [2, 3, 29, 223, 19037] ⟨6648063067, 2, [(2, 1), (3, 3), (29, 1), (223, 1), (19037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_223
    · exact prime_19037
  · decide +kernel

theorem prime_8271645703 : Nat.Prime 8271645703 := by
  apply nodeValid_prime [2, 3, 8233, 167449] ⟨8271645703, 6, [(2, 1), (3, 1), (8233, 1), (167449, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8233
    · exact prime_167449
  · decide +kernel

theorem prime_10520449627 : Nat.Prime 10520449627 := by
  apply nodeValid_prime [2, 3, 17, 103141663] ⟨10520449627, 2, [(2, 1), (3, 1), (17, 1), (103141663, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_103141663
  · decide +kernel

theorem prime_13682734823 : Nat.Prime 13682734823 := by
  apply nodeValid_prime [2, 19, 23, 101, 155003] ⟨13682734823, 5, [(2, 1), (19, 1), (23, 1), (101, 1), (155003, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_23
    · exact prime_101
    · exact prime_155003
  · decide +kernel

theorem prime_19513479269 : Nat.Prime 19513479269 := by
  apply nodeValid_prime [2, 787, 6198691] ⟨19513479269, 2, [(2, 2), (787, 1), (6198691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_787
    · exact prime_6198691
  · decide +kernel

theorem prime_345503129567 : Nat.Prime 345503129567 := by
  apply nodeValid_prime [2, 7, 547, 45116627] ⟨345503129567, 5, [(2, 1), (7, 1), (547, 1), (45116627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_547
    · exact prime_45116627
  · decide +kernel

theorem prime_345503129749 : Nat.Prime 345503129749 := by
  apply nodeValid_prime [2, 3, 7, 6491, 633667] ⟨345503129749, 6, [(2, 2), (3, 1), (7, 1), (6491, 1), (633667, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_6491
    · exact prime_633667
  · decide +kernel

theorem prime_345503158789 : Nat.Prime 345503158789 := by
  apply nodeValid_prime [2, 3, 67, 107, 4016171] ⟨345503158789, 6, [(2, 2), (3, 1), (67, 1), (107, 1), (4016171, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_67
    · exact prime_107
    · exact prime_4016171
  · decide +kernel

theorem prime_346137708467 : Nat.Prime 346137708467 := by
  apply nodeValid_prime [2, 11, 19699, 798697] ⟨346137708467, 2, [(2, 1), (11, 1), (19699, 1), (798697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_19699
    · exact prime_798697
  · decide +kernel

theorem prime_346137709517 : Nat.Prime 346137709517 := by
  apply nodeValid_prime [2, 181, 7207, 66337] ⟨346137709517, 2, [(2, 2), (181, 1), (7207, 1), (66337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_181
    · exact prime_7207
    · exact prime_66337
  · decide +kernel

theorem prime_346137717911 : Nat.Prime 346137717911 := by
  apply nodeValid_prime [2, 5, 17, 43, 1609, 29429] ⟨346137717911, 13, [(2, 1), (5, 1), (17, 1), (43, 1), (1609, 1), (29429, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_43
    · exact prime_1609
    · exact prime_29429
  · decide +kernel

theorem prime_346772987417 : Nat.Prime 346772987417 := by
  apply nodeValid_prime [2, 19, 2281401233] ⟨346772987417, 3, [(2, 3), (19, 1), (2281401233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_2281401233
  · decide +kernel

theorem prime_346772987849 : Nat.Prime 346772987849 := by
  apply nodeValid_prime [2, 7, 884624969] ⟨346772987849, 3, [(2, 3), (7, 2), (884624969, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_884624969
  · decide +kernel

theorem prime_346773058187 : Nat.Prime 346773058187 := by
  apply nodeValid_prime [2, 17977, 9644909] ⟨346773058187, 2, [(2, 1), (17977, 1), (9644909, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17977
    · exact prime_9644909
  · decide +kernel

theorem prime_347409118807 : Nat.Prime 347409118807 := by
  apply nodeValid_prime [2, 3, 17, 3405971753] ⟨347409118807, 3, [(2, 1), (3, 1), (17, 1), (3405971753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3405971753
  · decide +kernel

theorem prime_347409119527 : Nat.Prime 347409119527 := by
  apply nodeValid_prime [2, 3, 7, 8271645703] ⟨347409119527, 7, [(2, 1), (3, 1), (7, 1), (8271645703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_8271645703
  · decide +kernel

theorem prime_347409186743 : Nat.Prime 347409186743 := by
  apply nodeValid_prime [2, 227, 765218473] ⟨347409186743, 5, [(2, 1), (227, 1), (765218473, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_227
    · exact prime_765218473
  · decide +kernel

theorem prime_348046043117 : Nat.Prime 348046043117 := by
  apply nodeValid_prime [2, 149, 583969871] ⟨348046043117, 2, [(2, 2), (149, 1), (583969871, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_583969871
  · decide +kernel

theorem prime_348046046507 : Nat.Prime 348046046507 := by
  apply nodeValid_prime [2, 19, 59, 269, 577097] ⟨348046046507, 2, [(2, 1), (19, 1), (59, 1), (269, 1), (577097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_59
    · exact prime_269
    · exact prime_577097
  · decide +kernel

theorem prime_348046108379 : Nat.Prime 348046108379 := by
  apply nodeValid_prime [2, 149, 1167939961] ⟨348046108379, 2, [(2, 1), (149, 1), (1167939961, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_149
    · exact prime_1167939961
  · decide +kernel

theorem prime_348683787743 : Nat.Prime 348683787743 := by
  apply nodeValid_prime [2, 863, 12911, 15647] ⟨348683787743, 5, [(2, 1), (863, 1), (12911, 1), (15647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_863
    · exact prime_12911
    · exact prime_15647
  · decide +kernel

theorem prime_348683789063 : Nat.Prime 348683789063 := by
  apply nodeValid_prime [2, 7, 52639, 473147] ⟨348683789063, 5, [(2, 1), (7, 1), (52639, 1), (473147, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_52639
    · exact prime_473147
  · decide +kernel

theorem prime_348683825551 : Nat.Prime 348683825551 := by
  apply nodeValid_prime [2, 3, 5, 41, 56696557] ⟨348683825551, 3, [(2, 1), (3, 1), (5, 2), (41, 1), (56696557, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_56696557
  · decide +kernel

theorem prime_349322319221 : Nat.Prime 349322319221 := by
  apply nodeValid_prime [2, 5, 7, 431, 5789233] ⟨349322319221, 3, [(2, 2), (5, 1), (7, 1), (431, 1), (5789233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_431
    · exact prime_5789233
  · decide +kernel

theorem prime_349322319637 : Nat.Prime 349322319637 := by
  apply nodeValid_prime [2, 3, 19, 27689, 55333] ⟨349322319637, 2, [(2, 2), (3, 1), (19, 1), (27689, 1), (55333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_27689
    · exact prime_55333
  · decide +kernel

theorem prime_349322337523 : Nat.Prime 349322337523 := by
  apply nodeValid_prime [2, 3, 211, 91975339] ⟨349322337523, 2, [(2, 1), (3, 2), (211, 1), (91975339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_211
    · exact prime_91975339
  · decide +kernel

theorem prime_349961643529 : Nat.Prime 349961643529 := by
  apply nodeValid_prime [2, 3, 7, 14173, 146977] ⟨349961643529, 19, [(2, 3), (3, 1), (7, 1), (14173, 1), (146977, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_14173
    · exact prime_146977
  · decide +kernel

theorem prime_349961652847 : Nat.Prime 349961652847 := by
  apply nodeValid_prime [2, 3, 13, 498520873] ⟨349961652847, 3, [(2, 1), (3, 3), (13, 1), (498520873, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_498520873
  · decide +kernel

theorem prime_349961652917 : Nat.Prime 349961652917 := by
  apply nodeValid_prime [2, 19, 29, 158784779] ⟨349961652917, 2, [(2, 2), (19, 1), (29, 1), (158784779, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_158784779
  · decide +kernel

theorem prime_350601739687 : Nat.Prime 350601739687 := by
  apply nodeValid_prime [2, 3, 11, 139, 383, 11087] ⟨350601739687, 5, [(2, 1), (3, 3), (11, 1), (139, 1), (383, 1), (11087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_139
    · exact prime_383
    · exact prime_11087
  · decide +kernel

theorem prime_350601774823 : Nat.Prime 350601774823 := by
  apply nodeValid_prime [2, 3, 13, 449, 3336967] ⟨350601774823, 5, [(2, 1), (3, 2), (13, 1), (449, 1), (3336967, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_449
    · exact prime_3336967
  · decide +kernel

theorem prime_350601775061 : Nat.Prime 350601775061 := by
  apply nodeValid_prime [2, 5, 151, 2963, 39181] ⟨350601775061, 2, [(2, 2), (5, 1), (151, 1), (2963, 1), (39181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
    · exact prime_2963
    · exact prime_39181
  · decide +kernel

theorem prime_351242624801 : Nat.Prime 351242624801 := by
  apply nodeValid_prime [2, 5, 353, 613, 2029] ⟨351242624801, 6, [(2, 5), (5, 2), (353, 1), (613, 1), (2029, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_353
    · exact prime_613
    · exact prime_2029
  · decide +kernel

theorem prime_351242626843 : Nat.Prime 351242626843 := by
  apply nodeValid_prime [2, 3, 19513479269] ⟨351242626843, 2, [(2, 1), (3, 2), (19513479269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19513479269
  · decide +kernel

theorem prime_351242629429 : Nat.Prime 351242629429 := by
  apply nodeValid_prime [2, 3, 13567, 2157457] ⟨351242629429, 2, [(2, 2), (3, 1), (13567, 1), (2157457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13567
    · exact prime_2157457
  · decide +kernel

theorem prime_351884304269 : Nat.Prime 351884304269 := by
  apply nodeValid_prime [2, 7, 1795328083] ⟨351884304269, 2, [(2, 2), (7, 2), (1795328083, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1795328083
  · decide +kernel

theorem prime_351884328667 : Nat.Prime 351884328667 := by
  apply nodeValid_prime [2, 3, 13, 313, 647, 22277] ⟨351884328667, 3, [(2, 1), (3, 1), (13, 1), (313, 1), (647, 1), (22277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_313
    · exact prime_647
    · exact prime_22277
  · decide +kernel

theorem prime_351884329337 : Nat.Prime 351884329337 := by
  apply nodeValid_prime [2, 103, 427044089] ⟨351884329337, 3, [(2, 3), (103, 1), (427044089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_427044089
  · decide +kernel

theorem prime_352526782043 : Nat.Prime 352526782043 := by
  apply nodeValid_prime [2, 37, 32189, 147997] ⟨352526782043, 2, [(2, 1), (37, 1), (32189, 1), (147997, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_37
    · exact prime_32189
    · exact prime_147997
  · decide +kernel

theorem prime_352526797757 : Nat.Prime 352526797757 := by
  apply nodeValid_prime [2, 7, 1798606111] ⟨352526797757, 2, [(2, 2), (7, 2), (1798606111, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1798606111
  · decide +kernel

theorem prime_352526798573 : Nat.Prime 352526798573 := by
  apply nodeValid_prime [2, 13, 31, 2633, 6389] ⟨352526798573, 2, [(2, 2), (13, 2), (31, 1), (2633, 1), (6389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_31
    · exact prime_2633
    · exact prime_6389
  · decide +kernel

theorem prime_353170056271 : Nat.Prime 353170056271 := by
  apply nodeValid_prime [2, 3, 5, 2633, 4471073] ⟨353170056271, 3, [(2, 1), (3, 1), (5, 1), (2633, 1), (4471073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_2633
    · exact prime_4471073
  · decide +kernel

theorem prime_353170081861 : Nat.Prime 353170081861 := by
  apply nodeValid_prime [2, 3, 5, 4421, 1331411] ⟨353170081861, 2, [(2, 2), (3, 1), (5, 1), (4421, 1), (1331411, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4421
    · exact prime_1331411
  · decide +kernel

theorem prime_353170083377 : Nat.Prime 353170083377 := by
  apply nodeValid_prime [2, 11, 89, 4271, 5279] ⟨353170083377, 3, [(2, 4), (11, 1), (89, 1), (4271, 1), (5279, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_89
    · exact prime_4271
    · exact prime_5279
  · decide +kernel

theorem prime_353814101321 : Nat.Prime 353814101321 := by
  apply nodeValid_prime [2, 5, 449, 2939, 6703] ⟨353814101321, 11, [(2, 3), (5, 1), (449, 1), (2939, 1), (6703, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_449
    · exact prime_2939
    · exact prime_6703
  · decide +kernel

theorem prime_353814101593 : Nat.Prime 353814101593 := by
  apply nodeValid_prime [2, 3, 7, 37273, 56503] ⟨353814101593, 5, [(2, 3), (3, 1), (7, 1), (37273, 1), (56503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_37273
    · exact prime_56503
  · decide +kernel

theorem prime_353814124087 : Nat.Prime 353814124087 := by
  apply nodeValid_prime [2, 3, 2729, 29641] ⟨353814124087, 3, [(2, 1), (3, 7), (2729, 1), (29641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2729
    · exact prime_29641
  · decide +kernel

theorem prime_354458991097 : Nat.Prime 354458991097 := by
  apply nodeValid_prime [2, 3, 7, 17, 41370097] ⟨354458991097, 5, [(2, 3), (3, 2), (7, 1), (17, 1), (41370097, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_41370097
  · decide +kernel

theorem prime_354459001921 : Nat.Prime 354459001921 := by
  apply nodeValid_prime [2, 3, 5, 369228127] ⟨354459001921, 7, [(2, 6), (3, 1), (5, 1), (369228127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_369228127
  · decide +kernel

theorem prime_354459002071 : Nat.Prime 354459002071 := by
  apply nodeValid_prime [2, 3, 5, 101, 3203, 36523] ⟨354459002071, 3, [(2, 1), (3, 1), (5, 1), (101, 1), (3203, 1), (36523, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_3203
    · exact prime_36523
  · decide +kernel

theorem prime_355104641467 : Nat.Prime 355104641467 := by
  apply nodeValid_prime [2, 3, 1669, 3940091] ⟨355104641467, 3, [(2, 1), (3, 3), (1669, 1), (3940091, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1669
    · exact prime_3940091
  · decide +kernel

theorem prime_355104641503 : Nat.Prime 355104641503 := by
  apply nodeValid_prime [2, 3, 13, 29, 52329007] ⟨355104641503, 3, [(2, 1), (3, 2), (13, 1), (29, 1), (52329007, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_52329007
  · decide +kernel

theorem prime_355104649117 : Nat.Prime 355104649117 := by
  apply nodeValid_prime [2, 3, 7, 1409145433] ⟨355104649117, 5, [(2, 2), (3, 2), (7, 1), (1409145433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1409145433
  · decide +kernel

theorem prime_355751097551 : Nat.Prime 355751097551 := by
  apply nodeValid_prime [2, 5, 17, 79, 251, 21107] ⟨355751097551, 11, [(2, 1), (5, 2), (17, 1), (79, 1), (251, 1), (21107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_79
    · exact prime_251
    · exact prime_21107
  · decide +kernel

theorem prime_355751098267 : Nat.Prime 355751098267 := by
  apply nodeValid_prime [2, 3, 19, 164243351] ⟨355751098267, 3, [(2, 1), (3, 1), (19, 2), (164243351, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_164243351
  · decide +kernel

theorem prime_355751105399 : Nat.Prime 355751105399 := by
  apply nodeValid_prime [2, 13, 13682734823] ⟨355751105399, 7, [(2, 1), (13, 1), (13682734823, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_13682734823
  · decide +kernel

theorem prime_356398364921 : Nat.Prime 356398364921 := by
  apply nodeValid_prime [2, 5, 13, 19, 36072709] ⟨356398364921, 3, [(2, 3), (5, 1), (13, 1), (19, 1), (36072709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_19
    · exact prime_36072709
  · decide +kernel

theorem prime_356398392481 : Nat.Prime 356398392481 := by
  apply nodeValid_prime [2, 3, 5, 13, 59, 73, 89, 149] ⟨356398392481, 11, [(2, 5), (3, 1), (5, 1), (13, 1), (59, 1), (73, 1), (89, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_59
    · exact prime_73
    · exact prime_89
    · exact prime_149
  · decide +kernel

theorem prime_357046427321 : Nat.Prime 357046427321 := by
  apply nodeValid_prime [2, 5, 11, 61, 71, 17033] ⟨357046427321, 3, [(2, 3), (5, 1), (11, 2), (61, 1), (71, 1), (17033, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_61
    · exact prime_71
    · exact prime_17033
  · decide +kernel

theorem prime_357046450489 : Nat.Prime 357046450489 := by
  apply nodeValid_prime [2, 3, 7, 13, 54494269] ⟨357046450489, 23, [(2, 3), (3, 2), (7, 1), (13, 1), (54494269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_54494269
  · decide +kernel

theorem prime_357046451453 : Nat.Prime 357046451453 := by
  apply nodeValid_prime [2, 128201, 696263] ⟨357046451453, 2, [(2, 2), (128201, 1), (696263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_128201
    · exact prime_696263
  · decide +kernel

theorem prime_357695275087 : Nat.Prime 357695275087 := by
  apply nodeValid_prime [2, 3, 23, 19417, 44497] ⟨357695275087, 3, [(2, 1), (3, 2), (23, 1), (19417, 1), (44497, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_19417
    · exact prime_44497
  · decide +kernel

theorem prime_357695275271 : Nat.Prime 357695275271 := by
  apply nodeValid_prime [2, 5, 23, 109, 14267861] ⟨357695275271, 11, [(2, 1), (5, 1), (23, 1), (109, 1), (14267861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_23
    · exact prime_109
    · exact prime_14267861
  · decide +kernel

theorem prime_357695287319 : Nat.Prime 357695287319 := by
  apply nodeValid_prime [2, 17, 10520449627] ⟨357695287319, 13, [(2, 1), (17, 1), (10520449627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_10520449627
  · decide +kernel

theorem prime_358344891689 : Nat.Prime 358344891689 := by
  apply nodeValid_prime [2, 7, 59, 1451, 74747] ⟨358344891689, 6, [(2, 3), (7, 1), (59, 1), (1451, 1), (74747, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
    · exact prime_1451
    · exact prime_74747
  · decide +kernel

theorem prime_358344893663 : Nat.Prime 358344893663 := by
  apply nodeValid_prime [2, 7, 37, 2647, 261347] ⟨358344893663, 5, [(2, 1), (7, 1), (37, 1), (2647, 1), (261347, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_37
    · exact prime_2647
    · exact prime_261347
  · decide +kernel

theorem prime_358344949351 : Nat.Prime 358344949351 := by
  apply nodeValid_prime [2, 3, 5, 181, 3121, 4229] ⟨358344949351, 3, [(2, 1), (3, 1), (5, 2), (181, 1), (3121, 1), (4229, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_181
    · exact prime_3121
    · exact prime_4229
  · decide +kernel

theorem prime_358995374929 : Nat.Prime 358995374929 := by
  apply nodeValid_prime [2, 3, 2493023437] ⟨358995374929, 17, [(2, 4), (3, 2), (2493023437, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2493023437
  · decide +kernel

theorem prime_358995375293 : Nat.Prime 358995375293 := by
  apply nodeValid_prime [2, 224153, 400391] ⟨358995375293, 2, [(2, 2), (224153, 1), (400391, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_224153
    · exact prime_400391
  · decide +kernel

theorem prime_358995405619 : Nat.Prime 358995405619 := by
  apply nodeValid_prime [2, 3, 6648063067] ⟨358995405619, 2, [(2, 1), (3, 3), (6648063067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_6648063067
  · decide +kernel

theorem prime_359646640993 : Nat.Prime 359646640993 := by
  apply nodeValid_prime [2, 3, 1248773059] ⟨359646640993, 5, [(2, 5), (3, 2), (1248773059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1248773059
  · decide +kernel

theorem prime_359646653683 : Nat.Prime 359646653683 := by
  apply nodeValid_prime [2, 3, 41, 487326089] ⟨359646653683, 3, [(2, 1), (3, 2), (41, 1), (487326089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_487326089
  · decide +kernel

theorem prime_360298688887 : Nat.Prime 360298688887 := by
  apply nodeValid_prime [2, 3, 313, 7717, 8287] ⟨360298688887, 3, [(2, 1), (3, 2), (313, 1), (7717, 1), (8287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_313
    · exact prime_7717
    · exact prime_8287
  · decide +kernel

theorem prime_360298689589 : Nat.Prime 360298689589 := by
  apply nodeValid_prime [2, 3, 17, 3109, 189361] ⟨360298689589, 2, [(2, 2), (3, 2), (17, 1), (3109, 1), (189361, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_3109
    · exact prime_189361
  · decide +kernel

theorem prime_360298697653 : Nat.Prime 360298697653 := by
  apply nodeValid_prime [2, 3, 811, 12340687] ⟨360298697653, 5, [(2, 2), (3, 2), (811, 1), (12340687, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_811
    · exact prime_12340687
  · decide +kernel

theorem prime_360951523489 : Nat.Prime 360951523489 := by
  apply nodeValid_prime [2, 3, 59, 83, 9479] ⟨360951523489, 11, [(2, 5), (3, 5), (59, 1), (83, 1), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
    · exact prime_83
    · exact prime_9479
  · decide +kernel

theorem prime_360951524239 : Nat.Prime 360951524239 := by
  apply nodeValid_prime [2, 3, 2237, 26892529] ⟨360951524239, 3, [(2, 1), (3, 1), (2237, 1), (26892529, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2237
    · exact prime_26892529
  · decide +kernel

theorem prime_360951543769 : Nat.Prime 360951543769 := by
  apply nodeValid_prime [2, 3, 19, 241, 3284483] ⟨360951543769, 7, [(2, 3), (3, 1), (19, 1), (241, 1), (3284483, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_241
    · exact prime_3284483
  · decide +kernel

end Sude.Lucas.Generated
