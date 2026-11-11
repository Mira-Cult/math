import Sude.GeneratedPrefix.L8.Stage23

namespace Sude.GeneratedPrefix.L8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem endpoint_prime (x : (Fin 24 × Fin 8) × Bool) : Nat.Prime (endpoint x) := by
  rcases x with ⟨⟨j, i⟩, side⟩
  fin_cases j
  · exact Stage00.prime i side
  · exact Stage01.prime i side
  · exact Stage02.prime i side
  · exact Stage03.prime i side
  · exact Stage04.prime i side
  · exact Stage05.prime i side
  · exact Stage06.prime i side
  · exact Stage07.prime i side
  · exact Stage08.prime i side
  · exact Stage09.prime i side
  · exact Stage10.prime i side
  · exact Stage11.prime i side
  · exact Stage12.prime i side
  · exact Stage13.prime i side
  · exact Stage14.prime i side
  · exact Stage15.prime i side
  · exact Stage16.prime i side
  · exact Stage17.prime i side
  · exact Stage18.prime i side
  · exact Stage19.prime i side
  · exact Stage20.prime i side
  · exact Stage21.prime i side
  · exact Stage22.prime i side
  · exact Stage23.prime i side

theorem endpoint_in_pool (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (x : (Fin 24 × Fin 8) × Bool) : endpoint x ∈ pool n := by
  have hb := endpoint_bounds x
  exact finitePrefix_L_prime_in_pool lower hn (endpoint_prime x) hb.1 (by omega)

def poolValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    (Fin 24 × Fin 8) × Bool → pool n := fun x => ⟨endpoint x, endpoint_in_pool lower hn x⟩

theorem poolValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    Function.Injective (poolValues lower hn) := by
  intro x y h
  exact endpoint_injective (congrArg Subtype.val h)

theorem poolValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (j : Fin 24) (i : Fin 8) :
    (poolValues lower hn ((j, i), true)).val =
      (poolValues lower hn ((j, i), false)).val + 2 ^ (j.val + 1) := by
  simp [poolValues, endpoint]

end Sude.GeneratedPrefix.L8
