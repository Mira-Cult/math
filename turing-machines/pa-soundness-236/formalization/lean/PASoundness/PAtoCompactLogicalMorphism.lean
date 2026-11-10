import PASoundness.PAtoCompactGuardedTwoLogical

/-! A syntactic map preserving the logical operations carries checked
logical axioms to checked logical axioms. The map equations and the three
remaining guarded logical proof families are explicit inputs. This module
does not construct the map for multiplication reversal or any PA-axiom proof. -/

namespace PASoundness.PAtoCompactLogicalMorphism

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge

/-- The exact syntactic equations used for the eight logical axiom families.
No injectivity, involution, arithmetic equation, or truth preservation is
assumed. The equality of free-variable sets supplies the vacuity side condition. -/
structure LogicalMorphism where
  formula : Peano.Formula → Peano.Formula
  term : Peano.Term → Peano.Term
  imp : ∀ φ ψ, formula (φ.imp ψ) = (formula φ).imp (formula ψ)
  neg : ∀ φ, formula φ.not = (formula φ).not
  equal : ∀ t u, formula (t.equal u) = (term t).equal (term u)
  allAt : ∀ x φ, formula (FOL.allAt x φ) = FOL.allAt x (formula φ)
  substAt : ∀ φ x t, formula (FOL.substAt φ x t) = FOL.substAt (formula φ) x (term t)
  free : ∀ φ, (formula φ).freeVarFinset = φ.freeVarFinset

/-- A logical axiom remains a logical axiom after such a syntactic map. -/
theorem logical_axiom (m : LogicalMorphism) {φ : Peano.Formula}
    (h : FOL.LogicalAxiom φ) : FOL.LogicalAxiom (m.formula φ) := by
  cases h with
  | k φ ψ =>
      simpa only [m.imp] using FOL.LogicalAxiom.k (m.formula φ) (m.formula ψ)
  | s φ ψ χ =>
      simpa only [m.imp] using FOL.LogicalAxiom.s (m.formula φ) (m.formula ψ) (m.formula χ)
  | classical φ =>
      simpa only [m.imp, m.neg] using FOL.LogicalAxiom.classical (m.formula φ)
  | allElim φ x t =>
      simpa only [m.imp, m.allAt, m.substAt] using
        FOL.LogicalAxiom.allElim (m.formula φ) x (m.term t)
  | allImp φ ψ x =>
      simpa only [m.imp, m.allAt] using FOL.LogicalAxiom.allImp (m.formula φ) (m.formula ψ) x
  | vacuous φ x hx =>
      have hx' : x ∉ (m.formula φ).freeVarFinset := by simpa only [m.free] using hx
      simpa only [m.imp, m.allAt] using FOL.LogicalAxiom.vacuous (m.formula φ) x hx'
  | eqRefl t =>
      simpa only [m.equal] using FOL.LogicalAxiom.eqRefl (m.term t)
  | eqSubst φ x t u =>
      simpa only [m.imp, m.equal, m.substAt] using
        FOL.LogicalAxiom.eqSubst (m.formula φ) x (m.term t) (m.term u)

/-- Every checked logical leaf has a checked logical image. This is an
existence statement about finite syntax; it has no semantic soundness premise. -/
theorem logical_code_exists (m : LogicalMorphism)
    (c : Certificates.LogicalCode Peano.language) (φ : Peano.Formula)
    (hc : Certificates.logicalDecode c = some φ) :
    ∃ d, Certificates.logicalDecode d = some (m.formula φ) :=
  Certificates.logical_coverage (logical_axiom m (Certificates.logical_origin c φ hc))

/-- Compile the image of a checked logical leaf into finite K proof data,
conditional on the existing three guarded logical proof families. Choosing the
image code is noncomputable. No PA-axiom or PA-soundness input is used. -/
noncomputable def guarded_logical (m : LogicalMorphism)
    (h : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (c : Certificates.LogicalCode Peano.language) (φ : Peano.Formula)
    (hc : Certificates.logicalDecode c = some φ) :
    KDerivation (guardedCode (m.formula φ)) := by
  let hd := logical_code_exists m c φ hc
  let d := Classical.choose hd
  have hcheck : Certificates.logicalDecode d = some (m.formula φ) := Classical.choose_spec hd
  exact PAtoCompactGuardedPropositional.logicalHandler
    (PAtoCompactGuardedFourLogical.remainingLogical (PAtoCompactGuardedThreeLogical.fourLogical h))
    d (m.formula φ) hcheck

theorem guarded_logical_certificate (m : LogicalMorphism)
    (h : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (c : Certificates.LogicalCode Peano.language) (φ : Peano.Formula)
    (hc : Certificates.logicalDecode c = some φ) :
    theoremCode (certificate (guarded_logical m h c φ hc)) =
      guardedCode (m.formula φ) := certificate_correct _

end PASoundness.PAtoCompactLogicalMorphism

#print axioms PASoundness.PAtoCompactLogicalMorphism.logical_axiom
#print axioms PASoundness.PAtoCompactLogicalMorphism.logical_code_exists
#print axioms PASoundness.PAtoCompactLogicalMorphism.guarded_logical
#print axioms PASoundness.PAtoCompactLogicalMorphism.guarded_logical_certificate
