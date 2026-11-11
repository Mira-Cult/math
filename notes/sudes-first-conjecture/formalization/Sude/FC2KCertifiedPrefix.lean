import Sude.PrefixStageFamily
import Sude.PrefixTruncation
import Sude.FC2KExpanderPhysical

/-! Physical routing from a complete, globally separated L-prefix family. -/
namespace Sude
noncomputable section

theorem fullPrefixFit (n : ℕ) : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
theorem fullPrefixDiagonalFit (n : ℕ) : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
theorem fullPrefixRectangleFit : 24 * (4 * 6) ≤ 576 := by decide
theorem fullPrefixSquareFit {n : ℕ} (hn : 2001 ≤ n) : 2 * 576 + 1 ≤ n := by omega
def fullPrefixChoice : Fin 576 → Bool := fun _ => false
def fullPrefixRectangles {n : ℕ} (hn : 2001 ≤ n) : Finset (Cell n) :=
  allocatedBridgeRectangleSupport fullPrefixRectangleFit (fullPrefixSquareFit hn) fullPrefixChoice

def fullPrefixValues {n : ℕ} (hnmax : n ≤ 2400) (F : CertifiedPrefixFamily 24 14448 n) :
    (Fin 24 × Fin (6 * (n + 8))) × Bool → pool n :=
  truncatePrefixValues (by omega) F.values

theorem fullPrefixValues_injective {n : ℕ} (hnmax : n ≤ 2400)
    (F : CertifiedPrefixFamily 24 14448 n) : Function.Injective (fullPrefixValues hnmax F) :=
  truncatePrefixValues_injective (by omega) _ F.values_injective

theorem fullPrefixValues_gap {n : ℕ} (hnmax : n ≤ 2400)
    (F : CertifiedPrefixFamily 24 14448 n) :
    ∀ j i, (fullPrefixValues hnmax F ((j, i), true)).val =
      (fullPrefixValues hnmax F ((j, i), false)).val + 2 ^ (j.val + 1) :=
  truncatePrefixValues_gap (by omega) _ F.values_gap

/-- A concrete nonempty demand box within the parameterized bounds. -/
theorem fullPrefix_example_gates :
    2 * 2000 ≤ 2 ^ (24 + 1) - 2 ∧ 400000 * 994 < 199 * 999 * 2000 := by
  norm_num

/-- If all 24 stages and cross-stage separation are supplied, their actual
pool entries can be installed and used for integral row and column routing.
Packing is discharged for the whole L band. The chosen routing radius and
demand bound, prime diagonals, targets and completion remain explicit. -/
theorem fullPrefix_realizes_demands {n : ℕ} (hn : 2001 ≤ n) (hnmax : n ≤ 2400)
    (F : CertifiedPrefixFamily 24 14448 n) (a : Cell n ≃ Fin (n * n))
    (N B : ℕ) (hN : 2000 ≤ N) (hrad : 2 * N ≤ 2 ^ (24 + 1) - 2)
    (hB : 400000 * B < 199 * 999 * N) :
    ∃ b b₀ : Cell n ≃ Fin (n * n),
      (∀ x : Fin (24 * (4 * 6)) × Fin 4,
        entry b (packedRectangleCorner (fullPrefixSquareFit hn) fullPrefixChoice
          (Fin.castLE fullPrefixRectangleFit x.1, x.2)) =
            (fullPrefixValues hnmax F (prefixRectangleInput (fullPrefixDiagonalFit n) x)).val) ∧
      mainSum b₀ = mainSum b ∧ antiSum b₀ = antiSum b ∧
      (∀ c ∈ fullPrefixRectangles hn, entry b₀ c = entry b c) ∧
      ∀ dr dc : Fin n → ℤ,
      (∑ r, dr r = 0) → (∑ c, dc c = 0) →
      (∀ r, |dr r| ≤ (B : ℤ)) → (∀ c, |dc c| ≤ (B : ℤ)) →
      ∃ b' : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b' r : ℤ) - (rowSum b₀ r : ℤ) = 2 * dr r) ∧
        (∀ c, (columnSum b' c : ℤ) - (columnSum b₀ c : ℤ) = 2 * dc c) ∧
        mainSum b' = mainSum b₀ ∧ antiSum b' = antiSum b₀ ∧
        (∀ c ∈ fullPrefixRectangles hn, entry b' c = entry b₀ c) ∧
        Set.range (entry b') = pool n ∧ Function.Injective (entry b') := by
  have hcap : 4 * ((0 + 2) + 2 * (24 * 3) + 2 * (24 * 3)) + 8 < n := by omega
  obtain ⟨p, rows, cols, hrlen, hclen, b, _, hexp, hrmap, hcmap, hrpack, hcpack,
    _, hrect, _, _, hrowgap, hcolgap, _⟩ :=
    fc2k_install_expanding_prefix hn (fullPrefixFit n) (fullPrefixDiagonalFit n)
      fullPrefixRectangleFit (fullPrefixSquareFit hn) fullPrefixChoice (fullPrefixValues hnmax F)
      (fullPrefixValues_injective hnmax F) (fullPrefixValues_gap hnmax F) ∅ (by simp) ∅
      (by simp [LayerPacking.rowUsed]) (by simp [LayerPacking.colUsed]) hcap a (by simp) (by simp)
  have hr : LayerPacking.PackedLayers (fullPrefixRectangles hn) rows := by
    simpa [fullPrefixRectangles] using hrpack
  have hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (fullPrefixRectangles hn ∪ LayerPacking.layersSupport rows)) cols := by
    simpa [fullPrefixRectangles] using hcpack
  obtain ⟨b₀, hmain, hanti, hfixed, hrouting⟩ :=
    fc2k_route_installed_prefix b (fullPrefixRectangles hn) p hexp rows cols hrlen hclen
      hrmap hcmap hr hc hrowgap hcolgap N B hrad hN hB
  exact ⟨b, b₀, hrect, hmain, hanti, hfixed, hrouting⟩

end
end Sude
