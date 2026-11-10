import PASoundness.PAtoCompactScopedActiveDown
import PASoundness.PAtoCompactScopedActiveDownUniversal

/-! Structural alignment for downward replacement of an active name.
The target can already occur freely or alias another active name. -/
namespace PASoundness.PAtoCompactScopedActiveDownFull

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedActiveDown PASoundness.PAtoCompactScopedActiveDownUniversal
open PASoundness.PAtoCompactVacuousQuantifierFree

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- A lower target need not be fresh. The old active label must be absent
from the source formula's free variables so those free variables are not
changed by the named replacement. -/
noncomputable def scoped_active_down {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) : DownIH φ := by
  induction φ with
  | falsum =>
      intro bound i y hfree hdown
      exact ⟨identity 1, identity 1⟩
  | equal t u =>
      intro bound i y hfree hdown
      exact scoped_equal_active_down t u bound i y hfree hdown
  | rel r ts => exact nomatch r
  | imp a b iha ihb =>
      intro bound i y hfree hdown
      have hfa : bound i ∉ a.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have hfb : bound i ∉ b.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have aa := iha bound i y hfa hdown
      have bb := ihb bound i y hfb hdown
      change KBoth (.imp (replace (bound i) y (scopedFormula _ a bound))
          (replace (bound i) y (scopedFormula _ b bound)))
        (.imp (scopedFormula _ a (rename (bound i) y ∘ bound))
          (scopedFormula _ b (rename (bound i) y ∘ bound)))
      exact ⟨implicationCongr aa.2 bb.1, implicationCongr aa.1 bb.2⟩
  | all body ih =>
      exact universal_down_step body ih

theorem scoped_active_down_forward_certificate {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) (i : Fin n) (y : Nat)
    (hf : bound i ∉ φ.freeVarFinset) (hy : y < bound i) :
    theoremCode (certificate ((scoped_active_down φ bound i y hf hy).1)) =
      imp (replace (bound i) y (scopedFormula n φ bound)).encode
        (scopedFormula n φ (rename (bound i) y ∘ bound)).encode := certificate_correct _

theorem scoped_active_down_backward_certificate {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) (i : Fin n) (y : Nat)
    (hf : bound i ∉ φ.freeVarFinset) (hy : y < bound i) :
    theoremCode (certificate ((scoped_active_down φ bound i y hf hy).2)) =
      imp (scopedFormula n φ (rename (bound i) y ∘ bound)).encode
        (replace (bound i) y (scopedFormula n φ bound)).encode := certificate_correct _

end PASoundness.PAtoCompactScopedActiveDownFull

#print axioms PASoundness.PAtoCompactScopedActiveDownFull.scoped_active_down
#print axioms PASoundness.PAtoCompactScopedActiveDownFull.scoped_active_down_forward_certificate
#print axioms PASoundness.PAtoCompactScopedActiveDownFull.scoped_active_down_backward_certificate
