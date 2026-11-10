import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactExistsCommute

/-! Capture-safe exchange of the two literal bound witness names in a
translated equality matrix. The matrix's private binders must sit above a
fresh temporary name. -/
namespace PASoundness.PAtoCompactEqualitySwapWitnesses

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactExistsCommute

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exchange two bound names using a fresh temporary name. No assumptions on
any mathematical values represented by the names are involved. -/
def swap_bound_names (x y q : Nat) (f : Formula)
    (hxy : x ≠ y) (hqx : q ≠ x) (hqy : q ≠ y)
    (hxb : x ∉ f.binders) (hyb : y ∉ f.binders)
    (hqf : q ∉ f.names) :
    ProofEquiv (.ex y (.ex x f))
      (.ex x (.ex y (replace q x (replace x y (replace y q f))))) := by
  have hyb' : y ∉ (Formula.ex x f).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨Ne.symm hxy, hyb⟩
  have hqf' : q ∉ (Formula.ex x f).names := by
    simp only [Formula.names, Finset.mem_insert, not_or]
    exact ⟨hqx, hqf⟩
  have h1 := ProofEquiv.alphaExists y q (.ex x f) (Ne.symm hqy) hyb' hqf'
  have hxb1 : x ∉ (replace y q f).binders := by simpa [replace_binders] using hxb
  have hyf1 : y ∉ (replace y q f).names := replace_avoids y q f (Ne.symm hqy) hyb
  have h2 := ProofEquiv.alphaExists x y (replace y q f) hxy hxb1 hyf1
  have hqb2 : q ∉ (replace x y (replace y q f)).binders := by
    rw [replace_binders, replace_binders]
    exact fun h => hqf (f.binders_subset_names h)
  have hxf2 : x ∉ (replace x y (replace y q f)).names :=
    replace_avoids x y (replace y q f) hxy hxb1
  have hqbody : q ∉ (Formula.ex y (replace x y (replace y q f))).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨hqy, hqb2⟩
  have hxbody : x ∉ (Formula.ex y (replace x y (replace y q f))).names := by
    simp only [Formula.names, Finset.mem_insert, not_or]
    exact ⟨hxy, hxf2⟩
  have h3 := ProofEquiv.alphaExists q x (.ex y (replace x y (replace y q f))) hqx hqbody hxbody
  have h1' : ProofEquiv (.ex y (.ex x f)) (.ex q (.ex x (replace y q f))) := by
    simpa [replace, show x ≠ y by exact hxy] using h1
  have h3' : ProofEquiv (.ex q (.ex y (replace x y (replace y q f))))
      (.ex x (.ex y (replace q x (replace x y (replace y q f))))) := by
    simpa [replace, show y ≠ q by exact Ne.symm hqy] using h3
  exact (h1'.trans (ProofEquiv.existential q h2)).trans h3'

/-- Exchange the bound witness labels in an equality matrix, keeping the
matrix's operands and private blocks fixed. -/
def swap_matrix_witnesses {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b p q r : Nat)
    (hp : b+2 < p) (hq : b+2 < q) (hr : b+2 < r+2)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b) :
    ProofEquiv (.ex (b+1) (.ex b (matrix v t u (b+1) b p q r)))
      (.ex b (.ex (b+1) (matrix v t u b (b+1) p q r))) := by
  let M := matrix v t u (b+1) b p q r
  have hb : b ∉ M.binders := matrix_below_not_binder v t u (b+1) b p q r b (by omega) (by omega) (by omega)
  have hb1 : b+1 ∉ M.binders := matrix_below_not_binder v t u (b+1) b p q r (b+1) (by omega) (by omega) (by omega)
  have hbf : b+2 ∉ M.names := by
    apply matrix_fresh_gap v t u (b+1) b p q r (b+2) (by omega) (by omega) (by omega) (by omega) (by omega)
    · intro a ha; have := ht a ha; omega
    · intro a ha; have := hu a ha; omega
  have h := swap_bound_names b (b+1) (b+2) M (by omega) (by omega) (by omega) hb hb1 hbf
  have ht1 : ∀ a ∈ t.varFinset, v a ≠ b+1 := by intro a ha; have := ht a ha; omega
  have hu1 : ∀ a ∈ u.varFinset, v a ≠ b+1 := by intro a ha; have := hu a ha; omega
  have ht0 : ∀ a ∈ t.varFinset, v a ≠ b := by intro a ha; have := ht a ha; omega
  have hu0 : ∀ a ∈ u.varFinset, v a ≠ b := by intro a ha; have := hu a ha; omega
  have ht2 : ∀ a ∈ t.varFinset, v a ≠ b+2 := by intro a ha; have := ht a ha; omega
  have hu2 : ∀ a ∈ u.varFinset, v a ≠ b+2 := by intro a ha; have := hu a ha; omega
  have hrep : replace (b+2) b (replace b (b+1) (replace (b+1) (b+2) M)) =
      matrix v t u b (b+1) p q r := by
    dsimp [M]
    rw [matrix_replace_fresh_source v t u (b+1) b p q r (b+1) (b+2) (by omega) (by omega) (by omega) ht1 hu1]
    simp only [rename, ↓reduceIte, show b ≠ b+1 by omega]
    rw [matrix_replace_fresh_source v t u (b+2) b p q r b (b+1) (by omega) (by omega) (by omega) ht0 hu0]
    simp only [rename, ↓reduceIte, show b+2 ≠ b by omega]
    rw [matrix_replace_fresh_source v t u (b+2) (b+1) p q r (b+2) b (by omega) (by omega) (by omega) ht2 hu2]
    simp [rename]
  rw [hrep] at h
  exact h

#print axioms swap_bound_names
#print axioms swap_matrix_witnesses
end PASoundness.PAtoCompactEqualitySwapWitnesses
