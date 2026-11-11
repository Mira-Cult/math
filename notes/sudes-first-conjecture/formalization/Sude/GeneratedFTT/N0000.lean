import Sude.LucasCertificate

/-! Generated Lucas proof nodes; checked by Lean. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem prime_2 : Nat.Prime 2 := Nat.prime_two

theorem prime_3 : Nat.Prime 3 := by
  apply nodeValid_prime [2] ⟨3, 2, [(2, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact prime_2
  · decide +kernel

theorem prime_5 : Nat.Prime 5 := by
  apply nodeValid_prime [2] ⟨5, 2, [(2, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact prime_2
  · decide +kernel

theorem prime_7 : Nat.Prime 7 := by
  apply nodeValid_prime [2, 3] ⟨7, 3, [(2, 1), (3, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_11 : Nat.Prime 11 := by
  apply nodeValid_prime [2, 5] ⟨11, 2, [(2, 1), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_13 : Nat.Prime 13 := by
  apply nodeValid_prime [2, 3] ⟨13, 2, [(2, 2), (3, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_17 : Nat.Prime 17 := by
  apply nodeValid_prime [2] ⟨17, 3, [(2, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact prime_2
  · decide +kernel

theorem prime_19 : Nat.Prime 19 := by
  apply nodeValid_prime [2, 3] ⟨19, 2, [(2, 1), (3, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_23 : Nat.Prime 23 := by
  apply nodeValid_prime [2, 11] ⟨23, 5, [(2, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel

theorem prime_29 : Nat.Prime 29 := by
  apply nodeValid_prime [2, 7] ⟨29, 2, [(2, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7
  · decide +kernel

theorem prime_31 : Nat.Prime 31 := by
  apply nodeValid_prime [2, 3, 5] ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_37 : Nat.Prime 37 := by
  apply nodeValid_prime [2, 3] ⟨37, 2, [(2, 2), (3, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_41 : Nat.Prime 41 := by
  apply nodeValid_prime [2, 5] ⟨41, 6, [(2, 3), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_43 : Nat.Prime 43 := by
  apply nodeValid_prime [2, 3, 7] ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_47 : Nat.Prime 47 := by
  apply nodeValid_prime [2, 23] ⟨47, 5, [(2, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_23
  · decide +kernel

theorem prime_53 : Nat.Prime 53 := by
  apply nodeValid_prime [2, 13] ⟨53, 2, [(2, 2), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13
  · decide +kernel

theorem prime_59 : Nat.Prime 59 := by
  apply nodeValid_prime [2, 29] ⟨59, 2, [(2, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29
  · decide +kernel

theorem prime_61 : Nat.Prime 61 := by
  apply nodeValid_prime [2, 3, 5] ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_67 : Nat.Prime 67 := by
  apply nodeValid_prime [2, 3, 11] ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_71 : Nat.Prime 71 := by
  apply nodeValid_prime [2, 5, 7] ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_73 : Nat.Prime 73 := by
  apply nodeValid_prime [2, 3] ⟨73, 5, [(2, 3), (3, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_79 : Nat.Prime 79 := by
  apply nodeValid_prime [2, 3, 13] ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_83 : Nat.Prime 83 := by
  apply nodeValid_prime [2, 41] ⟨83, 2, [(2, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_41
  · decide +kernel

theorem prime_89 : Nat.Prime 89 := by
  apply nodeValid_prime [2, 11] ⟨89, 3, [(2, 3), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel

theorem prime_97 : Nat.Prime 97 := by
  apply nodeValid_prime [2, 3] ⟨97, 5, [(2, 5), (3, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_101 : Nat.Prime 101 := by
  apply nodeValid_prime [2, 5] ⟨101, 2, [(2, 2), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_103 : Nat.Prime 103 := by
  apply nodeValid_prime [2, 3, 17] ⟨103, 5, [(2, 1), (3, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_107 : Nat.Prime 107 := by
  apply nodeValid_prime [2, 53] ⟨107, 2, [(2, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53
  · decide +kernel

theorem prime_109 : Nat.Prime 109 := by
  apply nodeValid_prime [2, 3] ⟨109, 6, [(2, 2), (3, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_113 : Nat.Prime 113 := by
  apply nodeValid_prime [2, 7] ⟨113, 3, [(2, 4), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7
  · decide +kernel

theorem prime_127 : Nat.Prime 127 := by
  apply nodeValid_prime [2, 3, 7] ⟨127, 3, [(2, 1), (3, 2), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_131 : Nat.Prime 131 := by
  apply nodeValid_prime [2, 5, 13] ⟨131, 2, [(2, 1), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_137 : Nat.Prime 137 := by
  apply nodeValid_prime [2, 17] ⟨137, 3, [(2, 3), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17
  · decide +kernel

theorem prime_139 : Nat.Prime 139 := by
  apply nodeValid_prime [2, 3, 23] ⟨139, 2, [(2, 1), (3, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_149 : Nat.Prime 149 := by
  apply nodeValid_prime [2, 37] ⟨149, 2, [(2, 2), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37
  · decide +kernel

theorem prime_157 : Nat.Prime 157 := by
  apply nodeValid_prime [2, 3, 13] ⟨157, 5, [(2, 2), (3, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel

theorem prime_163 : Nat.Prime 163 := by
  apply nodeValid_prime [2, 3] ⟨163, 2, [(2, 1), (3, 4)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_167 : Nat.Prime 167 := by
  apply nodeValid_prime [2, 83] ⟨167, 5, [(2, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_83
  · decide +kernel

theorem prime_173 : Nat.Prime 173 := by
  apply nodeValid_prime [2, 43] ⟨173, 2, [(2, 2), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_43
  · decide +kernel

theorem prime_179 : Nat.Prime 179 := by
  apply nodeValid_prime [2, 89] ⟨179, 2, [(2, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_89
  · decide +kernel

theorem prime_181 : Nat.Prime 181 := by
  apply nodeValid_prime [2, 3, 5] ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_191 : Nat.Prime 191 := by
  apply nodeValid_prime [2, 5, 19] ⟨191, 19, [(2, 1), (5, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel

theorem prime_193 : Nat.Prime 193 := by
  apply nodeValid_prime [2, 3] ⟨193, 5, [(2, 6), (3, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_199 : Nat.Prime 199 := by
  apply nodeValid_prime [2, 3, 11] ⟨199, 3, [(2, 1), (3, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_233 : Nat.Prime 233 := by
  apply nodeValid_prime [2, 29] ⟨233, 3, [(2, 3), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_29
  · decide +kernel

theorem prime_241 : Nat.Prime 241 := by
  apply nodeValid_prime [2, 3, 5] ⟨241, 7, [(2, 4), (3, 1), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_251 : Nat.Prime 251 := by
  apply nodeValid_prime [2, 5] ⟨251, 6, [(2, 1), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_257 : Nat.Prime 257 := by
  apply nodeValid_prime [2] ⟨257, 3, [(2, 8)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact prime_2
  · decide +kernel

theorem prime_263 : Nat.Prime 263 := by
  apply nodeValid_prime [2, 131] ⟨263, 5, [(2, 1), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_131
  · decide +kernel

theorem prime_269 : Nat.Prime 269 := by
  apply nodeValid_prime [2, 67] ⟨269, 2, [(2, 2), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_67
  · decide +kernel

theorem prime_271 : Nat.Prime 271 := by
  apply nodeValid_prime [2, 3, 5] ⟨271, 6, [(2, 1), (3, 3), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_277 : Nat.Prime 277 := by
  apply nodeValid_prime [2, 3, 23] ⟨277, 5, [(2, 2), (3, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel

theorem prime_281 : Nat.Prime 281 := by
  apply nodeValid_prime [2, 5, 7] ⟨281, 3, [(2, 3), (5, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_283 : Nat.Prime 283 := by
  apply nodeValid_prime [2, 3, 47] ⟨283, 3, [(2, 1), (3, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_311 : Nat.Prime 311 := by
  apply nodeValid_prime [2, 5, 31] ⟨311, 17, [(2, 1), (5, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
  · decide +kernel

theorem prime_337 : Nat.Prime 337 := by
  apply nodeValid_prime [2, 3, 7] ⟨337, 10, [(2, 4), (3, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_347 : Nat.Prime 347 := by
  apply nodeValid_prime [2, 173] ⟨347, 2, [(2, 1), (173, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_173
  · decide +kernel

theorem prime_349 : Nat.Prime 349 := by
  apply nodeValid_prime [2, 3, 29] ⟨349, 2, [(2, 2), (3, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_353 : Nat.Prime 353 := by
  apply nodeValid_prime [2, 11] ⟨353, 3, [(2, 5), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel

theorem prime_359 : Nat.Prime 359 := by
  apply nodeValid_prime [2, 179] ⟨359, 7, [(2, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_179
  · decide +kernel

theorem prime_373 : Nat.Prime 373 := by
  apply nodeValid_prime [2, 3, 31] ⟨373, 2, [(2, 2), (3, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel

theorem prime_379 : Nat.Prime 379 := by
  apply nodeValid_prime [2, 3, 7] ⟨379, 2, [(2, 1), (3, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_389 : Nat.Prime 389 := by
  apply nodeValid_prime [2, 97] ⟨389, 2, [(2, 2), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_97
  · decide +kernel

theorem prime_397 : Nat.Prime 397 := by
  apply nodeValid_prime [2, 3, 11] ⟨397, 5, [(2, 2), (3, 2), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_433 : Nat.Prime 433 := by
  apply nodeValid_prime [2, 3] ⟨433, 5, [(2, 4), (3, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_443 : Nat.Prime 443 := by
  apply nodeValid_prime [2, 13, 17] ⟨443, 2, [(2, 1), (13, 1), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_17
  · decide +kernel

theorem prime_457 : Nat.Prime 457 := by
  apply nodeValid_prime [2, 3, 19] ⟨457, 13, [(2, 3), (3, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel

theorem prime_463 : Nat.Prime 463 := by
  apply nodeValid_prime [2, 3, 7, 11] ⟨463, 3, [(2, 1), (3, 1), (7, 1), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
  · decide +kernel

theorem prime_487 : Nat.Prime 487 := by
  apply nodeValid_prime [2, 3] ⟨487, 3, [(2, 1), (3, 5)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_491 : Nat.Prime 491 := by
  apply nodeValid_prime [2, 5, 7] ⟨491, 2, [(2, 1), (5, 1), (7, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel

theorem prime_499 : Nat.Prime 499 := by
  apply nodeValid_prime [2, 3, 83] ⟨499, 7, [(2, 1), (3, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_509 : Nat.Prime 509 := by
  apply nodeValid_prime [2, 127] ⟨509, 2, [(2, 2), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_127
  · decide +kernel

theorem prime_521 : Nat.Prime 521 := by
  apply nodeValid_prime [2, 5, 13] ⟨521, 3, [(2, 3), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_563 : Nat.Prime 563 := by
  apply nodeValid_prime [2, 281] ⟨563, 2, [(2, 1), (281, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_281
  · decide +kernel

theorem prime_577 : Nat.Prime 577 := by
  apply nodeValid_prime [2, 3] ⟨577, 5, [(2, 6), (3, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_593 : Nat.Prime 593 := by
  apply nodeValid_prime [2, 37] ⟨593, 3, [(2, 4), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_37
  · decide +kernel

theorem prime_599 : Nat.Prime 599 := by
  apply nodeValid_prime [2, 13, 23] ⟨599, 7, [(2, 1), (13, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
  · decide +kernel

theorem prime_601 : Nat.Prime 601 := by
  apply nodeValid_prime [2, 3, 5] ⟨601, 7, [(2, 3), (3, 1), (5, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_607 : Nat.Prime 607 := by
  apply nodeValid_prime [2, 3, 101] ⟨607, 3, [(2, 1), (3, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_613 : Nat.Prime 613 := by
  apply nodeValid_prime [2, 3, 17] ⟨613, 2, [(2, 2), (3, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel

theorem prime_641 : Nat.Prime 641 := by
  apply nodeValid_prime [2, 5] ⟨641, 3, [(2, 7), (5, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel

theorem prime_653 : Nat.Prime 653 := by
  apply nodeValid_prime [2, 163] ⟨653, 2, [(2, 2), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_163
  · decide +kernel

theorem prime_673 : Nat.Prime 673 := by
  apply nodeValid_prime [2, 3, 7] ⟨673, 5, [(2, 5), (3, 1), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_677 : Nat.Prime 677 := by
  apply nodeValid_prime [2, 13] ⟨677, 2, [(2, 2), (13, 2)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_13
  · decide +kernel

theorem prime_683 : Nat.Prime 683 := by
  apply nodeValid_prime [2, 11, 31] ⟨683, 5, [(2, 1), (11, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_31
  · decide +kernel

theorem prime_709 : Nat.Prime 709 := by
  apply nodeValid_prime [2, 3, 59] ⟨709, 2, [(2, 2), (3, 1), (59, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_59
  · decide +kernel

theorem prime_719 : Nat.Prime 719 := by
  apply nodeValid_prime [2, 359] ⟨719, 11, [(2, 1), (359, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_359
  · decide +kernel

theorem prime_739 : Nat.Prime 739 := by
  apply nodeValid_prime [2, 3, 41] ⟨739, 3, [(2, 1), (3, 2), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_751 : Nat.Prime 751 := by
  apply nodeValid_prime [2, 3, 5] ⟨751, 3, [(2, 1), (3, 1), (5, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel

theorem prime_757 : Nat.Prime 757 := by
  apply nodeValid_prime [2, 3, 7] ⟨757, 2, [(2, 2), (3, 3), (7, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel

theorem prime_821 : Nat.Prime 821 := by
  apply nodeValid_prime [2, 5, 41] ⟨821, 2, [(2, 2), (5, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
  · decide +kernel

theorem prime_911 : Nat.Prime 911 := by
  apply nodeValid_prime [2, 5, 7, 13] ⟨911, 17, [(2, 1), (5, 1), (7, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_13
  · decide +kernel

theorem prime_977 : Nat.Prime 977 := by
  apply nodeValid_prime [2, 61] ⟨977, 3, [(2, 4), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_61
  · decide +kernel

theorem prime_997 : Nat.Prime 997 := by
  apply nodeValid_prime [2, 3, 83] ⟨997, 7, [(2, 2), (3, 1), (83, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel

theorem prime_1049 : Nat.Prime 1049 := by
  apply nodeValid_prime [2, 131] ⟨1049, 3, [(2, 3), (131, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_131
  · decide +kernel

theorem prime_1129 : Nat.Prime 1129 := by
  apply nodeValid_prime [2, 3, 47] ⟨1129, 11, [(2, 3), (3, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel

theorem prime_1213 : Nat.Prime 1213 := by
  apply nodeValid_prime [2, 3, 101] ⟨1213, 2, [(2, 2), (3, 1), (101, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel

theorem prime_1259 : Nat.Prime 1259 := by
  apply nodeValid_prime [2, 17, 37] ⟨1259, 2, [(2, 1), (17, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
  · decide +kernel

theorem prime_1303 : Nat.Prime 1303 := by
  apply nodeValid_prime [2, 3, 7, 31] ⟨1303, 6, [(2, 1), (3, 1), (7, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
  · decide +kernel

theorem prime_1307 : Nat.Prime 1307 := by
  apply nodeValid_prime [2, 653] ⟨1307, 2, [(2, 1), (653, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_653
  · decide +kernel

theorem prime_1367 : Nat.Prime 1367 := by
  apply nodeValid_prime [2, 683] ⟨1367, 5, [(2, 1), (683, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_683
  · decide +kernel

theorem prime_1373 : Nat.Prime 1373 := by
  apply nodeValid_prime [2, 7] ⟨1373, 2, [(2, 2), (7, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_7
  · decide +kernel

theorem prime_1399 : Nat.Prime 1399 := by
  apply nodeValid_prime [2, 3, 233] ⟨1399, 13, [(2, 1), (3, 1), (233, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_233
  · decide +kernel

theorem prime_1409 : Nat.Prime 1409 := by
  apply nodeValid_prime [2, 11] ⟨1409, 3, [(2, 7), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel

theorem prime_1427 : Nat.Prime 1427 := by
  apply nodeValid_prime [2, 23, 31] ⟨1427, 2, [(2, 1), (23, 1), (31, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
  · decide +kernel

theorem prime_1447 : Nat.Prime 1447 := by
  apply nodeValid_prime [2, 3, 241] ⟨1447, 3, [(2, 1), (3, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel

theorem prime_1627 : Nat.Prime 1627 := by
  apply nodeValid_prime [2, 3, 271] ⟨1627, 3, [(2, 1), (3, 1), (271, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_271
  · decide +kernel

theorem prime_1697 : Nat.Prime 1697 := by
  apply nodeValid_prime [2, 53] ⟨1697, 3, [(2, 5), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_53
  · decide +kernel

theorem prime_1699 : Nat.Prime 1699 := by
  apply nodeValid_prime [2, 3, 283] ⟨1699, 3, [(2, 1), (3, 1), (283, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
  · decide +kernel

theorem prime_1733 : Nat.Prime 1733 := by
  apply nodeValid_prime [2, 433] ⟨1733, 2, [(2, 2), (433, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_433
  · decide +kernel

theorem prime_1741 : Nat.Prime 1741 := by
  apply nodeValid_prime [2, 3, 5, 29] ⟨1741, 2, [(2, 2), (3, 1), (5, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
  · decide +kernel

theorem prime_1783 : Nat.Prime 1783 := by
  apply nodeValid_prime [2, 3, 11] ⟨1783, 10, [(2, 1), (3, 4), (11, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel

theorem prime_1789 : Nat.Prime 1789 := by
  apply nodeValid_prime [2, 3, 149] ⟨1789, 6, [(2, 2), (3, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_149
  · decide +kernel

theorem prime_1811 : Nat.Prime 1811 := by
  apply nodeValid_prime [2, 5, 181] ⟨1811, 6, [(2, 1), (5, 1), (181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_181
  · decide +kernel

theorem prime_1931 : Nat.Prime 1931 := by
  apply nodeValid_prime [2, 5, 193] ⟨1931, 2, [(2, 1), (5, 1), (193, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_193
  · decide +kernel

theorem prime_1949 : Nat.Prime 1949 := by
  apply nodeValid_prime [2, 487] ⟨1949, 2, [(2, 2), (487, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_487
  · decide +kernel

theorem prime_2081 : Nat.Prime 2081 := by
  apply nodeValid_prime [2, 5, 13] ⟨2081, 3, [(2, 5), (5, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel

theorem prime_2087 : Nat.Prime 2087 := by
  apply nodeValid_prime [2, 7, 149] ⟨2087, 5, [(2, 1), (7, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_149
  · decide +kernel

theorem prime_2131 : Nat.Prime 2131 := by
  apply nodeValid_prime [2, 3, 5, 71] ⟨2131, 2, [(2, 1), (3, 1), (5, 1), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_71
  · decide +kernel

theorem prime_2273 : Nat.Prime 2273 := by
  apply nodeValid_prime [2, 71] ⟨2273, 3, [(2, 5), (71, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_71
  · decide +kernel

theorem prime_2339 : Nat.Prime 2339 := by
  apply nodeValid_prime [2, 7, 167] ⟨2339, 2, [(2, 1), (7, 1), (167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_167
  · decide +kernel

theorem prime_2467 : Nat.Prime 2467 := by
  apply nodeValid_prime [2, 3, 137] ⟨2467, 2, [(2, 1), (3, 2), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_137
  · decide +kernel

theorem prime_2543 : Nat.Prime 2543 := by
  apply nodeValid_prime [2, 31, 41] ⟨2543, 5, [(2, 1), (31, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_41
  · decide +kernel

theorem prime_2861 : Nat.Prime 2861 := by
  apply nodeValid_prime [2, 5, 11, 13] ⟨2861, 2, [(2, 2), (5, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_3011 : Nat.Prime 3011 := by
  apply nodeValid_prime [2, 5, 7, 43] ⟨3011, 2, [(2, 1), (5, 1), (7, 1), (43, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_43
  · decide +kernel

theorem prime_3049 : Nat.Prime 3049 := by
  apply nodeValid_prime [2, 3, 127] ⟨3049, 11, [(2, 3), (3, 1), (127, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_127
  · decide +kernel

theorem prime_3391 : Nat.Prime 3391 := by
  apply nodeValid_prime [2, 3, 5, 113] ⟨3391, 3, [(2, 1), (3, 1), (5, 1), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_113
  · decide +kernel

theorem prime_3457 : Nat.Prime 3457 := by
  apply nodeValid_prime [2, 3] ⟨3457, 7, [(2, 7), (3, 3)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel

theorem prime_3491 : Nat.Prime 3491 := by
  apply nodeValid_prime [2, 5, 349] ⟨3491, 2, [(2, 1), (5, 1), (349, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_349
  · decide +kernel

theorem prime_3617 : Nat.Prime 3617 := by
  apply nodeValid_prime [2, 113] ⟨3617, 3, [(2, 5), (113, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_113
  · decide +kernel

theorem prime_3847 : Nat.Prime 3847 := by
  apply nodeValid_prime [2, 3, 641] ⟨3847, 5, [(2, 1), (3, 1), (641, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_641
  · decide +kernel

theorem prime_3881 : Nat.Prime 3881 := by
  apply nodeValid_prime [2, 5, 97] ⟨3881, 13, [(2, 3), (5, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_97
  · decide +kernel

theorem prime_4073 : Nat.Prime 4073 := by
  apply nodeValid_prime [2, 509] ⟨4073, 3, [(2, 3), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_509
  · decide +kernel

theorem prime_4219 : Nat.Prime 4219 := by
  apply nodeValid_prime [2, 3, 19, 37] ⟨4219, 2, [(2, 1), (3, 1), (19, 1), (37, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_19
    · exact prime_37
  · decide +kernel

theorem prime_4273 : Nat.Prime 4273 := by
  apply nodeValid_prime [2, 3, 89] ⟨4273, 5, [(2, 4), (3, 1), (89, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · decide +kernel

theorem prime_4517 : Nat.Prime 4517 := by
  apply nodeValid_prime [2, 1129] ⟨4517, 2, [(2, 2), (1129, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1129
  · decide +kernel

theorem prime_4547 : Nat.Prime 4547 := by
  apply nodeValid_prime [2, 2273] ⟨4547, 2, [(2, 1), (2273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2273
  · decide +kernel

theorem prime_4831 : Nat.Prime 4831 := by
  apply nodeValid_prime [2, 3, 5, 7, 23] ⟨4831, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_4877 : Nat.Prime 4877 := by
  apply nodeValid_prime [2, 23, 53] ⟨4877, 2, [(2, 2), (23, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_53
  · decide +kernel

theorem prime_4889 : Nat.Prime 4889 := by
  apply nodeValid_prime [2, 13, 47] ⟨4889, 3, [(2, 3), (13, 1), (47, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_47
  · decide +kernel

theorem prime_5087 : Nat.Prime 5087 := by
  apply nodeValid_prime [2, 2543] ⟨5087, 5, [(2, 1), (2543, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2543
  · decide +kernel

theorem prime_5261 : Nat.Prime 5261 := by
  apply nodeValid_prime [2, 5, 263] ⟨5261, 2, [(2, 2), (5, 1), (263, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_263
  · decide +kernel

theorem prime_6299 : Nat.Prime 6299 := by
  apply nodeValid_prime [2, 47, 67] ⟨6299, 2, [(2, 1), (47, 1), (67, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_67
  · decide +kernel

theorem prime_7541 : Nat.Prime 7541 := by
  apply nodeValid_prime [2, 5, 13, 29] ⟨7541, 2, [(2, 2), (5, 1), (13, 1), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_29
  · decide +kernel

theorem prime_7873 : Nat.Prime 7873 := by
  apply nodeValid_prime [2, 3, 41] ⟨7873, 5, [(2, 6), (3, 1), (41, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_41
  · decide +kernel

theorem prime_9397 : Nat.Prime 9397 := by
  apply nodeValid_prime [2, 3, 29] ⟨9397, 2, [(2, 2), (3, 4), (29, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel

theorem prime_9479 : Nat.Prime 9479 := by
  apply nodeValid_prime [2, 7, 677] ⟨9479, 7, [(2, 1), (7, 1), (677, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_677
  · decide +kernel

theorem prime_9539 : Nat.Prime 9539 := by
  apply nodeValid_prime [2, 19, 251] ⟨9539, 2, [(2, 1), (19, 1), (251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_251
  · decide +kernel

theorem prime_9767 : Nat.Prime 9767 := by
  apply nodeValid_prime [2, 19, 257] ⟨9767, 5, [(2, 1), (19, 1), (257, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_257
  · decide +kernel

theorem prime_11587 : Nat.Prime 11587 := by
  apply nodeValid_prime [2, 3, 1931] ⟨11587, 2, [(2, 1), (3, 1), (1931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1931
  · decide +kernel

theorem prime_15271 : Nat.Prime 15271 := by
  apply nodeValid_prime [2, 3, 5, 509] ⟨15271, 11, [(2, 1), (3, 1), (5, 1), (509, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_509
  · decide +kernel

theorem prime_16067 : Nat.Prime 16067 := by
  apply nodeValid_prime [2, 29, 277] ⟨16067, 2, [(2, 1), (29, 1), (277, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_277
  · decide +kernel

theorem prime_17117 : Nat.Prime 17117 := by
  apply nodeValid_prime [2, 11, 389] ⟨17117, 3, [(2, 2), (11, 1), (389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_389
  · decide +kernel

theorem prime_17167 : Nat.Prime 17167 := by
  apply nodeValid_prime [2, 3, 2861] ⟨17167, 3, [(2, 1), (3, 1), (2861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2861
  · decide +kernel

theorem prime_17791 : Nat.Prime 17791 := by
  apply nodeValid_prime [2, 3, 5, 593] ⟨17791, 3, [(2, 1), (3, 1), (5, 1), (593, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_593
  · decide +kernel

theorem prime_18217 : Nat.Prime 18217 := by
  apply nodeValid_prime [2, 3, 11, 23] ⟨18217, 7, [(2, 3), (3, 2), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_18713 : Nat.Prime 18713 := by
  apply nodeValid_prime [2, 2339] ⟨18713, 3, [(2, 3), (2339, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2339
  · decide +kernel

theorem prime_20287 : Nat.Prime 20287 := by
  apply nodeValid_prime [2, 3, 7, 23] ⟨20287, 5, [(2, 1), (3, 2), (7, 2), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_23
  · decide +kernel

theorem prime_20389 : Nat.Prime 20389 := by
  apply nodeValid_prime [2, 3, 1699] ⟨20389, 6, [(2, 2), (3, 1), (1699, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1699
  · decide +kernel

theorem prime_20639 : Nat.Prime 20639 := by
  apply nodeValid_prime [2, 17, 607] ⟨20639, 11, [(2, 1), (17, 1), (607, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_607
  · decide +kernel

theorem prime_20983 : Nat.Prime 20983 := by
  apply nodeValid_prime [2, 3, 13, 269] ⟨20983, 3, [(2, 1), (3, 1), (13, 1), (269, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_269
  · decide +kernel

theorem prime_21839 : Nat.Prime 21839 := by
  apply nodeValid_prime [2, 61, 179] ⟨21839, 11, [(2, 1), (61, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_61
    · exact prime_179
  · decide +kernel

theorem prime_25121 : Nat.Prime 25121 := by
  apply nodeValid_prime [2, 5, 157] ⟨25121, 3, [(2, 5), (5, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_157
  · decide +kernel

theorem prime_25639 : Nat.Prime 25639 := by
  apply nodeValid_prime [2, 3, 4273] ⟨25639, 3, [(2, 1), (3, 1), (4273, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4273
  · decide +kernel

theorem prime_27647 : Nat.Prime 27647 := by
  apply nodeValid_prime [2, 23, 601] ⟨27647, 5, [(2, 1), (23, 1), (601, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_601
  · decide +kernel

theorem prime_28181 : Nat.Prime 28181 := by
  apply nodeValid_prime [2, 5, 1409] ⟨28181, 2, [(2, 2), (5, 1), (1409, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1409
  · decide +kernel

theorem prime_36037 : Nat.Prime 36037 := by
  apply nodeValid_prime [2, 3, 7, 11, 13] ⟨36037, 2, [(2, 2), (3, 2), (7, 1), (11, 1), (13, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
  · decide +kernel

theorem prime_37589 : Nat.Prime 37589 := by
  apply nodeValid_prime [2, 9397] ⟨37589, 2, [(2, 2), (9397, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9397
  · decide +kernel

theorem prime_44179 : Nat.Prime 44179 := by
  apply nodeValid_prime [2, 3, 37, 199] ⟨44179, 2, [(2, 1), (3, 1), (37, 1), (199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
    · exact prime_199
  · decide +kernel

theorem prime_45247 : Nat.Prime 45247 := by
  apply nodeValid_prime [2, 3, 7541] ⟨45247, 5, [(2, 1), (3, 1), (7541, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7541
  · decide +kernel

theorem prime_49411 : Nat.Prime 49411 := by
  apply nodeValid_prime [2, 3, 5, 61] ⟨49411, 2, [(2, 1), (3, 4), (5, 1), (61, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_61
  · decide +kernel

theorem prime_50093 : Nat.Prime 50093 := by
  apply nodeValid_prime [2, 7, 1789] ⟨50093, 2, [(2, 2), (7, 1), (1789, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1789
  · decide +kernel

theorem prime_56941 : Nat.Prime 56941 := by
  apply nodeValid_prime [2, 3, 5, 13, 73] ⟨56941, 2, [(2, 2), (3, 1), (5, 1), (13, 1), (73, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_73
  · decide +kernel

theorem prime_57427 : Nat.Prime 57427 := by
  apply nodeValid_prime [2, 3, 17, 563] ⟨57427, 2, [(2, 1), (3, 1), (17, 1), (563, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_563
  · decide +kernel

theorem prime_57457 : Nat.Prime 57457 := by
  apply nodeValid_prime [2, 3, 7, 19] ⟨57457, 5, [(2, 4), (3, 3), (7, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
  · decide +kernel

theorem prime_58603 : Nat.Prime 58603 := by
  apply nodeValid_prime [2, 3, 9767] ⟨58603, 2, [(2, 1), (3, 1), (9767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_9767
  · decide +kernel

theorem prime_62201 : Nat.Prime 62201 := by
  apply nodeValid_prime [2, 5, 311] ⟨62201, 3, [(2, 3), (5, 2), (311, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_311
  · decide +kernel

theorem prime_64781 : Nat.Prime 64781 := by
  apply nodeValid_prime [2, 5, 41, 79] ⟨64781, 2, [(2, 2), (5, 1), (41, 1), (79, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_41
    · exact prime_79
  · decide +kernel

theorem prime_75833 : Nat.Prime 75833 := by
  apply nodeValid_prime [2, 9479] ⟨75833, 3, [(2, 3), (9479, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_9479
  · decide +kernel

theorem prime_79823 : Nat.Prime 79823 := by
  apply nodeValid_prime [2, 107, 373] ⟨79823, 5, [(2, 1), (107, 1), (373, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_107
    · exact prime_373
  · decide +kernel

theorem prime_105503 : Nat.Prime 105503 := by
  apply nodeValid_prime [2, 17, 29, 107] ⟨105503, 10, [(2, 1), (17, 1), (29, 1), (107, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_107
  · decide +kernel

theorem prime_106747 : Nat.Prime 106747 := by
  apply nodeValid_prime [2, 3, 17791] ⟨106747, 2, [(2, 1), (3, 1), (17791, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17791
  · decide +kernel

theorem prime_125899 : Nat.Prime 125899 := by
  apply nodeValid_prime [2, 3, 20983] ⟨125899, 2, [(2, 1), (3, 1), (20983, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_20983
  · decide +kernel

theorem prime_162787 : Nat.Prime 162787 := by
  apply nodeValid_prime [2, 3, 13, 2087] ⟨162787, 3, [(2, 1), (3, 1), (13, 1), (2087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_2087
  · decide +kernel

theorem prime_178093 : Nat.Prime 178093 := by
  apply nodeValid_prime [2, 3, 17, 97] ⟨178093, 2, [(2, 2), (3, 3), (17, 1), (97, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_97
  · decide +kernel

theorem prime_188999 : Nat.Prime 188999 := by
  apply nodeValid_prime [2, 53, 1783] ⟨188999, 13, [(2, 1), (53, 1), (1783, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_53
    · exact prime_1783
  · decide +kernel

theorem prime_204931 : Nat.Prime 204931 := by
  apply nodeValid_prime [2, 3, 5, 11, 23] ⟨204931, 2, [(2, 1), (3, 4), (5, 1), (11, 1), (23, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_23
  · decide +kernel

theorem prime_206551 : Nat.Prime 206551 := by
  apply nodeValid_prime [2, 3, 5, 17] ⟨206551, 11, [(2, 1), (3, 5), (5, 2), (17, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · decide +kernel

theorem prime_244177 : Nat.Prime 244177 := by
  apply nodeValid_prime [2, 3, 5087] ⟨244177, 5, [(2, 4), (3, 1), (5087, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5087
  · decide +kernel

theorem prime_328127 : Nat.Prime 328127 := by
  apply nodeValid_prime [2, 359, 457] ⟨328127, 5, [(2, 1), (359, 1), (457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_359
    · exact prime_457
  · decide +kernel

theorem prime_438733 : Nat.Prime 438733 := by
  apply nodeValid_prime [2, 3, 7, 1741] ⟨438733, 2, [(2, 2), (3, 2), (7, 1), (1741, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1741
  · decide +kernel

theorem prime_461891 : Nat.Prime 461891 := by
  apply nodeValid_prime [2, 5, 11, 13, 17, 19] ⟨461891, 18, [(2, 1), (5, 1), (11, 1), (13, 1), (17, 1), (19, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_17
    · exact prime_19
  · decide +kernel

theorem prime_492047 : Nat.Prime 492047 := by
  apply nodeValid_prime [2, 347, 709] ⟨492047, 5, [(2, 1), (347, 1), (709, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_347
    · exact prime_709
  · decide +kernel

theorem prime_529751 : Nat.Prime 529751 := by
  apply nodeValid_prime [2, 5, 13, 163] ⟨529751, 17, [(2, 1), (5, 3), (13, 1), (163, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_163
  · decide +kernel

theorem prime_557533 : Nat.Prime 557533 := by
  apply nodeValid_prime [2, 3, 17, 911] ⟨557533, 5, [(2, 2), (3, 2), (17, 1), (911, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_911
  · decide +kernel

theorem prime_579721 : Nat.Prime 579721 := by
  apply nodeValid_prime [2, 3, 5, 4831] ⟨579721, 11, [(2, 3), (3, 1), (5, 1), (4831, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_4831
  · decide +kernel

theorem prime_727247 : Nat.Prime 727247 := by
  apply nodeValid_prime [2, 13, 83, 337] ⟨727247, 5, [(2, 1), (13, 1), (83, 1), (337, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_83
    · exact prime_337
  · decide +kernel

theorem prime_780841 : Nat.Prime 780841 := by
  apply nodeValid_prime [2, 3, 5, 241] ⟨780841, 7, [(2, 3), (3, 4), (5, 1), (241, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_241
  · decide +kernel

theorem prime_783599 : Nat.Prime 783599 := by
  apply nodeValid_prime [2, 17, 19, 1213] ⟨783599, 11, [(2, 1), (17, 1), (19, 1), (1213, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
    · exact prime_1213
  · decide +kernel

theorem prime_846059 : Nat.Prime 846059 := by
  apply nodeValid_prime [2, 109, 3881] ⟨846059, 2, [(2, 1), (109, 1), (3881, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_3881
  · decide +kernel

theorem prime_984707 : Nat.Prime 984707 := by
  apply nodeValid_prime [2, 109, 4517] ⟨984707, 2, [(2, 1), (109, 1), (4517, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_109
    · exact prime_4517
  · decide +kernel

theorem prime_1002289 : Nat.Prime 1002289 := by
  apply nodeValid_prime [2, 3, 7, 19, 157] ⟨1002289, 11, [(2, 4), (3, 1), (7, 1), (19, 1), (157, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_19
    · exact prime_157
  · decide +kernel

theorem prime_1059503 : Nat.Prime 1059503 := by
  apply nodeValid_prime [2, 529751] ⟨1059503, 5, [(2, 1), (529751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_529751
  · decide +kernel

theorem prime_1158679 : Nat.Prime 1158679 := by
  apply nodeValid_prime [2, 3, 43, 499] ⟨1158679, 3, [(2, 1), (3, 3), (43, 1), (499, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_499
  · decide +kernel

theorem prime_1515169 : Nat.Prime 1515169 := by
  apply nodeValid_prime [2, 3, 5261] ⟨1515169, 11, [(2, 5), (3, 2), (5261, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5261
  · decide +kernel

theorem prime_1952519 : Nat.Prime 1952519 := by
  apply nodeValid_prime [2, 17, 57427] ⟨1952519, 7, [(2, 1), (17, 1), (57427, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_57427
  · decide +kernel

theorem prime_2231711 : Nat.Prime 2231711 := by
  apply nodeValid_prime [2, 5, 13, 17167] ⟨2231711, 19, [(2, 1), (5, 1), (13, 1), (17167, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17167
  · decide +kernel

theorem prime_2799733 : Nat.Prime 2799733 := by
  apply nodeValid_prime [2, 3, 13, 131, 137] ⟨2799733, 5, [(2, 2), (3, 1), (13, 1), (131, 1), (137, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_131
    · exact prime_137
  · decide +kernel

theorem prime_2952283 : Nat.Prime 2952283 := by
  apply nodeValid_prime [2, 3, 492047] ⟨2952283, 2, [(2, 1), (3, 1), (492047, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_492047
  · decide +kernel

theorem prime_3222041 : Nat.Prime 3222041 := by
  apply nodeValid_prime [2, 5, 109, 739] ⟨3222041, 3, [(2, 3), (5, 1), (109, 1), (739, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_109
    · exact prime_739
  · decide +kernel

theorem prime_3235753 : Nat.Prime 3235753 := by
  apply nodeValid_prime [2, 3, 13, 3457] ⟨3235753, 5, [(2, 3), (3, 2), (13, 1), (3457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_3457
  · decide +kernel

theorem prime_4439917 : Nat.Prime 4439917 := by
  apply nodeValid_prime [2, 3, 13, 53, 179] ⟨4439917, 2, [(2, 2), (3, 2), (13, 1), (53, 1), (179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_179
  · decide +kernel

theorem prime_6963199 : Nat.Prime 6963199 := by
  apply nodeValid_prime [2, 3, 11, 105503] ⟨6963199, 11, [(2, 1), (3, 1), (11, 1), (105503, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_105503
  · decide +kernel

theorem prime_7391701 : Nat.Prime 7391701 := by
  apply nodeValid_prime [2, 3, 5, 43, 191] ⟨7391701, 13, [(2, 2), (3, 2), (5, 2), (43, 1), (191, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_43
    · exact prime_191
  · decide +kernel

theorem prime_9606251 : Nat.Prime 9606251 := by
  apply nodeValid_prime [2, 5, 29, 53] ⟨9606251, 2, [(2, 1), (5, 5), (29, 1), (53, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_53
  · decide +kernel

theorem prime_10565861 : Nat.Prime 10565861 := by
  apply nodeValid_prime [2, 5, 29, 18217] ⟨10565861, 2, [(2, 2), (5, 1), (29, 1), (18217, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_18217
  · decide +kernel

theorem prime_20767207 : Nat.Prime 20767207 := by
  apply nodeValid_prime [2, 3, 23, 61, 2467] ⟨20767207, 5, [(2, 1), (3, 1), (23, 1), (61, 1), (2467, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_61
    · exact prime_2467
  · decide +kernel

theorem prime_25602383 : Nat.Prime 25602383 := by
  apply nodeValid_prime [2, 13, 984707] ⟨25602383, 7, [(2, 1), (13, 1), (984707, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_984707
  · decide +kernel

theorem prime_26959721 : Nat.Prime 26959721 := by
  apply nodeValid_prime [2, 5, 107, 6299] ⟨26959721, 3, [(2, 3), (5, 1), (107, 1), (6299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_6299
  · decide +kernel

theorem prime_30755093 : Nat.Prime 30755093 := by
  apply nodeValid_prime [2, 379, 20287] ⟨30755093, 2, [(2, 2), (379, 1), (20287, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_379
    · exact prime_20287
  · decide +kernel

theorem prime_32635457 : Nat.Prime 32635457 := by
  apply nodeValid_prime [2, 7, 97, 751] ⟨32635457, 5, [(2, 6), (7, 1), (97, 1), (751, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_97
    · exact prime_751
  · decide +kernel

theorem prime_34171693 : Nat.Prime 34171693 := by
  apply nodeValid_prime [2, 3, 103, 27647] ⟨34171693, 2, [(2, 2), (3, 1), (103, 1), (27647, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_103
    · exact prime_27647
  · decide +kernel

theorem prime_36258913 : Nat.Prime 36258913 := by
  apply nodeValid_prime [2, 3, 125899] ⟨36258913, 5, [(2, 5), (3, 2), (125899, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_125899
  · decide +kernel

theorem prime_47144159 : Nat.Prime 47144159 := by
  apply nodeValid_prime [2, 23, 977, 1049] ⟨47144159, 17, [(2, 1), (23, 1), (977, 1), (1049, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_977
    · exact prime_1049
  · decide +kernel

theorem prime_51204767 : Nat.Prime 51204767 := by
  apply nodeValid_prime [2, 25602383] ⟨51204767, 5, [(2, 1), (25602383, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_25602383
  · decide +kernel

theorem prime_63826123 : Nat.Prime 63826123 := by
  apply nodeValid_prime [2, 3, 283, 37589] ⟨63826123, 3, [(2, 1), (3, 1), (283, 1), (37589, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_283
    · exact prime_37589
  · decide +kernel

theorem prime_69161089 : Nat.Prime 69161089 := by
  apply nodeValid_prime [2, 3, 389, 463] ⟨69161089, 11, [(2, 7), (3, 1), (389, 1), (463, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_389
    · exact prime_463
  · decide +kernel

theorem prime_126790333 : Nat.Prime 126790333 := by
  apply nodeValid_prime [2, 3, 10565861] ⟨126790333, 2, [(2, 2), (3, 1), (10565861, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10565861
  · decide +kernel

theorem prime_139622519 : Nat.Prime 139622519 := by
  apply nodeValid_prime [2, 7, 397, 25121] ⟨139622519, 7, [(2, 1), (7, 1), (397, 1), (25121, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_397
    · exact prime_25121
  · decide +kernel

theorem prime_151861763 : Nat.Prime 151861763 := by
  apply nodeValid_prime [2, 13, 283, 20639] ⟨151861763, 2, [(2, 1), (13, 1), (283, 1), (20639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_283
    · exact prime_20639
  · decide +kernel

theorem prime_184421177 : Nat.Prime 184421177 := by
  apply nodeValid_prime [2, 23, 1002289] ⟨184421177, 3, [(2, 3), (23, 1), (1002289, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_1002289
  · decide +kernel

theorem prime_187952749 : Nat.Prime 187952749 := by
  apply nodeValid_prime [2, 3, 17, 37, 673] ⟨187952749, 2, [(2, 2), (3, 1), (17, 1), (37, 2), (673, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_37
    · exact prime_673
  · decide +kernel

theorem prime_196356691 : Nat.Prime 196356691 := by
  apply nodeValid_prime [2, 3, 5, 727247] ⟨196356691, 2, [(2, 1), (3, 3), (5, 1), (727247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_727247
  · decide +kernel

theorem prime_323601737 : Nat.Prime 323601737 := by
  apply nodeValid_prime [2, 3491, 11587] ⟨323601737, 3, [(2, 3), (3491, 1), (11587, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3491
    · exact prime_11587
  · decide +kernel

theorem prime_335890897 : Nat.Prime 335890897 := by
  apply nodeValid_prime [2, 3, 11, 17, 23, 1627] ⟨335890897, 5, [(2, 4), (3, 1), (11, 1), (17, 1), (23, 1), (1627, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_23
    · exact prime_1627
  · decide +kernel

theorem prime_401763827 : Nat.Prime 401763827 := by
  apply nodeValid_prime [2, 4547, 44179] ⟨401763827, 2, [(2, 1), (4547, 1), (44179, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_4547
    · exact prime_44179
  · decide +kernel

theorem prime_640614307 : Nat.Prime 640614307 := by
  apply nodeValid_prime [2, 3, 521, 204931] ⟨640614307, 2, [(2, 1), (3, 1), (521, 1), (204931, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_521
    · exact prime_204931
  · decide +kernel

theorem prime_1067764993 : Nat.Prime 1067764993 := by
  apply nodeValid_prime [2, 3, 7, 31, 43, 149] ⟨1067764993, 5, [(2, 8), (3, 1), (7, 1), (31, 1), (43, 1), (149, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_43
    · exact prime_149
  · decide +kernel

theorem prime_1109050721 : Nat.Prime 1109050721 := by
  apply nodeValid_prime [2, 5, 107, 64781] ⟨1109050721, 3, [(2, 5), (5, 1), (107, 1), (64781, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_107
    · exact prime_64781
  · decide +kernel

theorem prime_1142487343 : Nat.Prime 1142487343 := by
  apply nodeValid_prime [2, 3, 783599] ⟨1142487343, 5, [(2, 1), (3, 6), (783599, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_783599
  · decide +kernel

theorem prime_1222977629 : Nat.Prime 1222977629 := by
  apply nodeValid_prime [2, 137, 2231711] ⟨1222977629, 2, [(2, 2), (137, 1), (2231711, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_137
    · exact prime_2231711
  · decide +kernel

theorem prime_4231627357 : Nat.Prime 4231627357 := by
  apply nodeValid_prime [2, 3, 11, 563, 56941] ⟨4231627357, 2, [(2, 2), (3, 1), (11, 1), (563, 1), (56941, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_563
    · exact prime_56941
  · decide +kernel

theorem prime_4337472523 : Nat.Prime 4337472523 := by
  apply nodeValid_prime [2, 3, 29, 43, 579721] ⟨4337472523, 2, [(2, 1), (3, 1), (29, 1), (43, 1), (579721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_43
    · exact prime_579721
  · decide +kernel

theorem prime_5730096989 : Nat.Prime 5730096989 := by
  apply nodeValid_prime [2, 7, 11, 19, 577, 1697] ⟨5730096989, 2, [(2, 2), (7, 1), (11, 1), (19, 1), (577, 1), (1697, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_11
    · exact prime_19
    · exact prime_577
    · exact prime_1697
  · decide +kernel

theorem prime_11354463073 : Nat.Prime 11354463073 := by
  apply nodeValid_prime [2, 3, 1399, 28181] ⟨11354463073, 11, [(2, 5), (3, 2), (1399, 1), (28181, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1399
    · exact prime_28181
  · decide +kernel

theorem prime_11781401461 : Nat.Prime 11781401461 := by
  apply nodeValid_prime [2, 3, 5, 196356691] ⟨11781401461, 2, [(2, 2), (3, 1), (5, 1), (196356691, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_196356691
  · decide +kernel

theorem prime_17296586317 : Nat.Prime 17296586317 := by
  apply nodeValid_prime [2, 3, 23, 6963199] ⟨17296586317, 2, [(2, 2), (3, 3), (23, 1), (6963199, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_6963199
  · decide +kernel

theorem prime_17726204203 : Nat.Prime 17726204203 := by
  apply nodeValid_prime [2, 3, 7, 757, 557533] ⟨17726204203, 2, [(2, 1), (3, 1), (7, 1), (757, 1), (557533, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_757
    · exact prime_557533
  · decide +kernel

theorem prime_35452407569 : Nat.Prime 35452407569 := by
  apply nodeValid_prime [2, 47, 47144159] ⟨35452407569, 3, [(2, 4), (47, 1), (47144159, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_47144159
  · decide +kernel

theorem prime_65834615813 : Nat.Prime 65834615813 := by
  apply nodeValid_prime [2, 7, 335890897] ⟨65834615813, 2, [(2, 2), (7, 2), (335890897, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_335890897
  · decide +kernel

theorem prime_65834630539 : Nat.Prime 65834630539 := by
  apply nodeValid_prime [2, 3, 3391, 3235753] ⟨65834630539, 2, [(2, 1), (3, 1), (3391, 1), (3235753, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3391
    · exact prime_3235753
  · decide +kernel

theorem prime_65834631041 : Nat.Prime 65834631041 := by
  apply nodeValid_prime [2, 5, 79, 719, 1811] ⟨65834631041, 3, [(2, 7), (5, 1), (79, 1), (719, 1), (1811, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_79
    · exact prime_719
    · exact prime_1811
  · decide +kernel

theorem prime_66040786561 : Nat.Prime 66040786561 := by
  apply nodeValid_prime [2, 3, 5, 7, 241, 20389] ⟨66040786561, 19, [(2, 7), (3, 1), (5, 1), (7, 1), (241, 1), (20389, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_241
    · exact prime_20389
  · decide +kernel

theorem prime_66040786577 : Nat.Prime 66040786577 := by
  apply nodeValid_prime [2, 21839, 188999] ⟨66040786577, 3, [(2, 4), (21839, 1), (188999, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_21839
    · exact prime_188999
  · decide +kernel

theorem prime_66040791967 : Nat.Prime 66040791967 := by
  apply nodeValid_prime [2, 3, 1222977629] ⟨66040791967, 3, [(2, 1), (3, 3), (1222977629, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1222977629
  · decide +kernel

theorem prime_66247390327 : Nat.Prime 66247390327 := by
  apply nodeValid_prime [2, 3, 13, 19, 251, 178093] ⟨66247390327, 3, [(2, 1), (3, 1), (13, 1), (19, 1), (251, 1), (178093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_251
    · exact prime_178093
  · decide +kernel

theorem prime_66247390331 : Nat.Prime 66247390331 := by
  apply nodeValid_prime [2, 5, 11, 29, 20767207] ⟨66247390331, 6, [(2, 1), (5, 1), (11, 1), (29, 1), (20767207, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
    · exact prime_20767207
  · decide +kernel

theorem prime_66247407757 : Nat.Prime 66247407757 := by
  apply nodeValid_prime [2, 3, 613, 997, 3011] ⟨66247407757, 5, [(2, 2), (3, 2), (613, 1), (997, 1), (3011, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_613
    · exact prime_997
    · exact prime_3011
  · decide +kernel

theorem prime_66454461629 : Nat.Prime 66454461629 := by
  apply nodeValid_prime [2, 43, 139, 173, 16067] ⟨66454461629, 2, [(2, 2), (43, 1), (139, 1), (173, 1), (16067, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_139
    · exact prime_173
    · exact prime_16067
  · decide +kernel

theorem prime_66454462489 : Nat.Prime 66454462489 := by
  apply nodeValid_prime [2, 3, 23, 43, 2799733] ⟨66454462489, 11, [(2, 3), (3, 1), (23, 1), (43, 1), (2799733, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_43
    · exact prime_2799733
  · decide +kernel

theorem prime_66661956143 : Nat.Prime 66661956143 := by
  apply nodeValid_prime [2, 31, 18713, 57457] ⟨66661956143, 5, [(2, 1), (31, 1), (18713, 1), (57457, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_18713
    · exact prime_57457
  · decide +kernel

theorem prime_66661957823 : Nat.Prime 66661957823 := by
  apply nodeValid_prime [2, 103, 323601737] ⟨66661957823, 5, [(2, 1), (103, 1), (323601737, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_103
    · exact prime_323601737
  · decide +kernel

theorem prime_66661957853 : Nat.Prime 66661957853 := by
  apply nodeValid_prime [2, 7, 3049, 780841] ⟨66661957853, 2, [(2, 2), (7, 1), (3049, 1), (780841, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3049
    · exact prime_780841
  · decide +kernel

theorem prime_66869868313 : Nat.Prime 66869868313 := by
  apply nodeValid_prime [2, 3, 13, 29, 67, 83, 443] ⟨66869868313, 5, [(2, 3), (3, 2), (13, 1), (29, 1), (67, 1), (83, 1), (443, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_67
    · exact prime_83
    · exact prime_443
  · decide +kernel

theorem prime_66869870713 : Nat.Prime 66869870713 := by
  apply nodeValid_prime [2, 3, 1427, 1952519] ⟨66869870713, 10, [(2, 3), (3, 1), (1427, 1), (1952519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1427
    · exact prime_1952519
  · decide +kernel

theorem prime_66869890799 : Nat.Prime 66869890799 := by
  apply nodeValid_prime [2, 47, 61, 199, 58603] ⟨66869890799, 17, [(2, 1), (47, 1), (61, 1), (199, 1), (58603, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_61
    · exact prime_199
    · exact prime_58603
  · decide +kernel

theorem prime_67078244669 : Nat.Prime 67078244669 := by
  apply nodeValid_prime [2, 41, 353, 1158679] ⟨67078244669, 2, [(2, 2), (41, 1), (353, 1), (1158679, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_353
    · exact prime_1158679
  · decide +kernel

theorem prime_67078244771 : Nat.Prime 67078244771 := by
  apply nodeValid_prime [2, 5, 131, 51204767] ⟨67078244771, 10, [(2, 1), (5, 1), (131, 1), (51204767, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_131
    · exact prime_51204767
  · decide +kernel

theorem prime_67078266037 : Nat.Prime 67078266037 := by
  apply nodeValid_prime [2, 3, 1259, 4439917] ⟨67078266037, 2, [(2, 2), (3, 1), (1259, 1), (4439917, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1259
    · exact prime_4439917
  · decide +kernel

theorem prime_67287072271 : Nat.Prime 67287072271 := by
  apply nodeValid_prime [2, 3, 5, 11, 241, 846059] ⟨67287072271, 11, [(2, 1), (3, 1), (5, 1), (11, 1), (241, 1), (846059, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
    · exact prime_241
    · exact prime_846059
  · decide +kernel

theorem prime_67287072329 : Nat.Prime 67287072329 := by
  apply nodeValid_prime [2, 7, 179, 1373, 4889] ⟨67287072329, 3, [(2, 3), (7, 1), (179, 1), (1373, 1), (4889, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_179
    · exact prime_1373
    · exact prime_4889
  · decide +kernel

theorem prime_67287084143 : Nat.Prime 67287084143 := by
  apply nodeValid_prime [2, 179, 187952749] ⟨67287084143, 5, [(2, 1), (179, 1), (187952749, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_179
    · exact prime_187952749
  · decide +kernel

theorem prime_67496322679 : Nat.Prime 67496322679 := by
  apply nodeValid_prime [2, 3, 107, 509, 206551] ⟨67496322679, 6, [(2, 1), (3, 1), (107, 1), (509, 1), (206551, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_107
    · exact prime_509
    · exact prime_206551
  · decide +kernel

theorem prime_67496322937 : Nat.Prime 67496322937 := by
  apply nodeValid_prime [2, 3, 7, 401763827] ⟨67496322937, 5, [(2, 3), (3, 1), (7, 1), (401763827, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_401763827
  · decide +kernel

theorem prime_67496342371 : Nat.Prime 67496342371 := by
  apply nodeValid_prime [2, 3, 5, 163, 1447, 9539] ⟨67496342371, 12, [(2, 1), (3, 1), (5, 1), (163, 1), (1447, 1), (9539, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_163
    · exact prime_1447
    · exact prime_9539
  · decide +kernel

theorem prime_67706037713 : Nat.Prime 67706037713 := by
  apply nodeValid_prime [2, 4231627357] ⟨67706037713, 3, [(2, 4), (4231627357, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_4231627357
  · decide +kernel

theorem prime_67706037823 : Nat.Prime 67706037823 := by
  apply nodeValid_prime [2, 3, 89, 126790333] ⟨67706037823, 3, [(2, 1), (3, 1), (89, 1), (126790333, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_89
    · exact prime_126790333
  · decide +kernel

theorem prime_67706043467 : Nat.Prime 67706043467 := by
  apply nodeValid_prime [2, 29, 71, 101, 162787] ⟨67706043467, 2, [(2, 1), (29, 1), (71, 1), (101, 1), (162787, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_29
    · exact prime_71
    · exact prime_101
    · exact prime_162787
  · decide +kernel

theorem prime_67916189399 : Nat.Prime 67916189399 := by
  apply nodeValid_prime [2, 491, 69161089] ⟨67916189399, 7, [(2, 1), (491, 1), (69161089, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_491
    · exact prime_69161089
  · decide +kernel

theorem prime_67916194571 : Nat.Prime 67916194571 := by
  apply nodeValid_prime [2, 5, 7, 101, 9606251] ⟨67916194571, 7, [(2, 1), (5, 1), (7, 1), (101, 1), (9606251, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_101
    · exact prime_9606251
  · decide +kernel

theorem prime_67916195089 : Nat.Prime 67916195089 := by
  apply nodeValid_prime [2, 3, 7, 71, 79, 36037] ⟨67916195089, 17, [(2, 4), (3, 1), (7, 1), (71, 1), (79, 1), (36037, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_71
    · exact prime_79
    · exact prime_36037
  · decide +kernel

theorem prime_68126771407 : Nat.Prime 68126771407 := by
  apply nodeValid_prime [2, 3, 29, 15271, 25639] ⟨68126771407, 3, [(2, 1), (3, 1), (29, 1), (15271, 1), (25639, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_29
    · exact prime_15271
    · exact prime_25639
  · decide +kernel

theorem prime_68126778439 : Nat.Prime 68126778439 := by
  apply nodeValid_prime [2, 3, 11354463073] ⟨68126778439, 3, [(2, 1), (3, 1), (11354463073, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11354463073
  · decide +kernel

theorem prime_68126779009 : Nat.Prime 68126779009 := by
  apply nodeValid_prime [2, 3, 1307, 45247] ⟨68126779009, 31, [(2, 7), (3, 2), (1307, 1), (45247, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1307
    · exact prime_45247
  · decide +kernel

theorem prime_68337793351 : Nat.Prime 68337793351 := by
  apply nodeValid_prime [2, 3, 5, 151861763] ⟨68337793351, 6, [(2, 1), (3, 2), (5, 2), (151861763, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_151861763
  · decide +kernel

theorem prime_68337816647 : Nat.Prime 68337816647 := by
  apply nodeValid_prime [2, 11, 101, 30755093] ⟨68337816647, 5, [(2, 1), (11, 1), (101, 1), (30755093, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_101
    · exact prime_30755093
  · decide +kernel

theorem prime_68337816991 : Nat.Prime 68337816991 := by
  apply nodeValid_prime [2, 3, 5, 19, 491, 244177] ⟨68337816991, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (491, 1), (244177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_491
    · exact prime_244177
  · decide +kernel

theorem prime_68549240581 : Nat.Prime 68549240581 := by
  apply nodeValid_prime [2, 3, 5, 1142487343] ⟨68549240581, 7, [(2, 2), (3, 1), (5, 1), (1142487343, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_1142487343
  · decide +kernel

theorem prime_68549243311 : Nat.Prime 68549243311 := by
  apply nodeValid_prime [2, 3, 5, 17, 97, 461891] ⟨68549243311, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (97, 1), (461891, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_97
    · exact prime_461891
  · decide +kernel

theorem prime_68549256103 : Nat.Prime 68549256103 := by
  apply nodeValid_prime [2, 3, 179, 63826123] ⟨68549256103, 3, [(2, 1), (3, 1), (179, 1), (63826123, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_63826123
  · decide +kernel

theorem prime_68761144703 : Nat.Prime 68761144703 := by
  apply nodeValid_prime [2, 31, 1109050721] ⟨68761144703, 5, [(2, 1), (31, 1), (1109050721, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_31
    · exact prime_1109050721
  · decide +kernel

theorem prime_68761144883 : Nat.Prime 68761144883 := by
  apply nodeValid_prime [2, 1949, 3617, 4877] ⟨68761144883, 2, [(2, 1), (1949, 1), (3617, 1), (4877, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_1949
    · exact prime_3617
    · exact prime_4877
  · decide +kernel

theorem prime_68761163869 : Nat.Prime 68761163869 := by
  apply nodeValid_prime [2, 3, 5730096989] ⟨68761163869, 2, [(2, 2), (3, 1), (5730096989, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5730096989
  · decide +kernel

theorem prime_68973520199 : Nat.Prime 68973520199 := by
  apply nodeValid_prime [2, 11, 17, 184421177] ⟨68973520199, 11, [(2, 1), (11, 1), (17, 1), (184421177, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_184421177
  · decide +kernel

theorem prime_68973523219 : Nat.Prime 68973523219 := by
  apply nodeValid_prime [2, 3, 281, 1515169] ⟨68973523219, 3, [(2, 1), (3, 4), (281, 1), (1515169, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_281
    · exact prime_1515169
  · decide +kernel

theorem prime_68973524387 : Nat.Prime 68973524387 := by
  apply nodeValid_prime [2, 13, 19, 139622519] ⟨68973524387, 2, [(2, 1), (13, 1), (19, 1), (139622519, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_19
    · exact prime_139622519
  · decide +kernel

theorem prime_69186321361 : Nat.Prime 69186321361 := by
  apply nodeValid_prime [2, 3, 5, 13, 7391701] ⟨69186321361, 28, [(2, 4), (3, 2), (5, 1), (13, 1), (7391701, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_7391701
  · decide +kernel

theorem prime_69186345157 : Nat.Prime 69186345157 := by
  apply nodeValid_prime [2, 3, 640614307] ⟨69186345157, 2, [(2, 2), (3, 3), (640614307, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_640614307
  · decide +kernel

theorem prime_69186345269 : Nat.Prime 69186345269 := by
  apply nodeValid_prime [2, 17296586317] ⟨69186345269, 2, [(2, 2), (17296586317, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_17296586317
  · decide +kernel

theorem prime_69399559483 : Nat.Prime 69399559483 := by
  apply nodeValid_prime [2, 3, 11, 29, 36258913] ⟨69399559483, 2, [(2, 1), (3, 1), (11, 1), (29, 1), (36258913, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_29
    · exact prime_36258913
  · decide +kernel

end Sude.Lucas.Generated
