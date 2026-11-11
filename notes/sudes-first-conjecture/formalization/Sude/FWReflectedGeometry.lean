import Sude.ReflectedBinGeometry
import Sude.FWFiniteGates
import Sude.FWPoolBound

/-! Exact FW6--FW7 reflected-bin geometry for the frozen parameters. -/
namespace Sude
noncomputable section

/-- The lower-band starting point for FW's `A=235`, `N=16`. -/
def fwReflectedLowAnchor (m X : ℝ) : ℝ :=
  m - ((16 / 235 : ℝ) + 1 / 3 + 16 / 235) * X

/-- The upper-band ending point, reflected about the actual pool mean. -/
def fwReflectedHighAnchor (m X : ℝ) : ℝ :=
  m + ((16 / 235 : ℝ) + 1 / 3 + 16 / 235) * X

/-- Each half-open bin has length `2δX`, with `δ=1/235`. -/
def fwReflectedStep (X : ℝ) : ℝ := (2 / 235 : ℝ) * X

def fwReflectedLeft (m X : ℝ) : Fin 16 × Bool → ℝ :=
  reflectedBinLeft (fwReflectedLowAnchor m X) (fwReflectedHighAnchor m X) (fwReflectedStep X)

def fwReflectedRight (m X : ℝ) : Fin 16 × Bool → ℝ :=
  reflectedBinRight (fwReflectedLowAnchor m X) (fwReflectedHighAnchor m X) (fwReflectedStep X)

/-- FW's reflected bins lie inside `[1,X]`, are pairwise separated, and
have the source's matched-pair midpoint and gap bounds. The mean interval
is an explicit hypothesis, not an imported project-specific corollary. -/
theorem fw_reflected_bin_geometry (m X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X) :
    (∀ z, 1 ≤ fwReflectedLeft m X z ∧ fwReflectedLeft m X z ≤ fwReflectedRight m X z ∧
      fwReflectedRight m X z ≤ X) ∧
    (∀ z t, z ≠ t → fwReflectedRight m X z ≤ fwReflectedLeft m X t ∨
      fwReflectedRight m X t ≤ fwReflectedLeft m X z) ∧
    (∀ i j, fwReflectedRight m X (i, false) ≤ fwReflectedLeft m X (j, true)) ∧
    (∀ i p q, fwReflectedLeft m X (i, false) < p → p ≤ fwReflectedRight m X (i, false) →
      fwReflectedLeft m X (i, true) < q → q ≤ fwReflectedRight m X (i, true) →
      |(p + q) / 2 - m| ≤ X / 235 ∧ (2 / 3 : ℝ) * X ≤ q - p ∧
        q - p ≤ (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X) := by
  let L := fwReflectedLowAnchor m X
  let U := fwReflectedHighAnchor m X
  let t := fwReflectedStep X
  have ht : 0 < t := by dsimp [t, fwReflectedStep]; nlinarith
  have hL : 1 ≤ L := by dsimp [L, fwReflectedLowAnchor]; norm_num; nlinarith
  have hU : U ≤ X := by dsimp [U, fwReflectedHighAnchor]; norm_num; nlinarith
  have hsep : L + (16 : ℝ) * t ≤ U - 16 * t := by
    dsimp [L, U, t, fwReflectedLowAnchor, fwReflectedHighAnchor, fwReflectedStep]
    norm_num
    nlinarith
  have hmid : (L + U) / 2 = m := by
    dsimp [L, U, fwReflectedLowAnchor, fwReflectedHighAnchor]
    ring
  have ht2 : t / 2 = X / 235 := by dsimp [t, fwReflectedStep]; ring
  have hgapLo : U - L - 2 * (16 : ℝ) * t = (2 / 3 : ℝ) * X := by
    dsimp [L, U, t, fwReflectedLowAnchor, fwReflectedHighAnchor, fwReflectedStep]
    ring
  have hgapHi : U - L = (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X := by
    dsimp [L, U, fwReflectedLowAnchor, fwReflectedHighAnchor]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact reflected_bin_endpoint_bounds L U t X hL ht hsep hU
  · exact reflected_bin_pairwise_separated L U t ht hsep
  · exact reflected_bin_cross_separated L U t ht hsep
  · intro i p q hpl hpr hql hqr
    have h := reflected_bin_pair_bounds L U t ht i p q ⟨hpl, hpr⟩ ⟨hql, hqr⟩
    rw [hmid, ht2] at h
    have hLo := h.2.1
    norm_num only [Nat.cast_ofNat] at hLo
    refine ⟨h.1, ?_, ?_⟩
    · linarith [hgapLo]
    · linarith [h.2.2, hgapHi]

end
end Sude
