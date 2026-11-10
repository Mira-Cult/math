import PASoundness.PAtoCompactUnarySubstitutionReduce
import PASoundness.PAtoCompactScopedAddZeroComplete
import PASoundness.PAtoCompactRightZeroTermFunctional
import PASoundness.PAtoCompactRightZeroTermTotality
import PASoundness.PAtoCompactAddZeroGraphOutput
import PASoundness.PAtoCompactUnaryAllElimComplete

/-! Universal elimination from a concrete term graph and its two graph laws.
The inputs are required only in the source-variable occurrence branch. -/
namespace PASoundness.PAtoCompactRightZeroAllElim

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactUnarySubstitutionReduce
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactScopedAddZeroComplete
open PASoundness.PAtoCompactRightZeroTermGrammar

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Given the explicit graph laws and guarded graph existence for a concrete
term, construct the guarded universal-elimination proof. None of the graph
inputs is required when the replaced variable does not occur. -/
noncomputable def allElim_of_graph_laws (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (total : x ∈ φ.freeVarFinset →
      KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
        (existsCode (outputName (allElimFormula φ x t))
          (termGraph id t (outputName (allElimFormula φ x t))
            (allocatorBase (allElimFormula φ x t))).encode)))
    (output : x ∈ φ.freeVarFinset → OutputTransport t)
    (functional : x ∈ φ.freeVarFinset → GuardFunctionality (guardFormula (allElimFormula φ x t)) t) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  apply allElim_of_variable_graph φ x t total
  intro hx
  let A := allElimFormula φ x t
  let q := outputName A
  let d := allocatorBase A
  let g := guardFormula A
  have hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hx ha
  have hlt : ∀ a ∈ t.varFinset, a < guardBase A := by
    intro a ha
    have hle : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) (hcover a ha)
    unfold guardBase
    omega
  have hqd : q < d := by dsimp [q, d, allocatorBase]; omega
  have htd : ∀ a ∈ t.varFinset, a < d := by
    intro a ha
    have h := hlt a ha
    dsimp [d, allocatorBase, outputName]
    omega
  have hdom (a : Nat) (ha : a ∈ t.varFinset) :
      KDerivation (imp g.encode (domainAt d a).encode) := by
    have h := PASoundness.PAtoCompactGuardedEqualityReflexivity.guardFormula_projection
      A a (hcover a ha)
    exact compose h (domainAt_transport (guardBase A) d a (by have := hlt a ha; omega)
      (by have := htd a ha; omega))
  have halign := (formula_replacement_substitution g t x q d hqd htd hdom
    (output hx) (functional hx) φ).1
  change KDerivation (imp g.encode (imp (termGraph id t q d).encode
    (imp (code (FOL.substAt φ x (.var q))) (code (FOL.substAt φ x t)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph id t q d).encode
  let V := code (FOL.substAt φ x (.var q))
  let Γ := [V, G, g.encode]
  have hv : Context Γ V := Context.head _ _
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hret : Context Γ (retained g t q d).encode := by
    have hh := Context.conjunctionIntro hg hG
    simpa [retained, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, G] using hh
  exact .mp hv (.mp hret (.closed halign))

theorem allElim_of_graph_laws_certificate (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (total : x ∈ φ.freeVarFinset →
      KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
        (existsCode (outputName (allElimFormula φ x t))
          (termGraph id t (outputName (allElimFormula φ x t))
            (allocatorBase (allElimFormula φ x t))).encode)))
    (output : x ∈ φ.freeVarFinset → OutputTransport t)
    (functional : x ∈ φ.freeVarFinset → GuardFunctionality (guardFormula (allElimFormula φ x t)) t) :
    theoremCode (certificate (allElim_of_graph_laws φ x t total output functional)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

/-- Universal elimination for unary terms followed by any finite number of
right-zero additions. Every case constructs finite K proof data. -/
noncomputable def rightZero_allElim (φ : Peano.Formula) (x : Nat)
    {t : Peano.Term} (ht : RightZeroTerm t) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  cases ht with
  | unary h => exact PASoundness.PAtoCompactUnaryAllElimComplete.unary_allElim φ x h
  | @addZero u h =>
      let T : Peano.Term := .func .add ![u, .func .zero Fin.elim0]
      have hT : RightZeroTerm T := RightZeroTerm.addZero h
      change KDerivation (guardedCode (allElimFormula φ x T))
      apply allElim_of_graph_laws φ x T
      · intro hx
        apply PASoundness.PAtoCompactRightZeroTermTotality.canonical_total id (allElimFormula φ x T) hT
        intro a ha
        exact termVars_in_axiom_of_occurs φ x T hx ha
      · intro _hx b q r hq hr hv
        exact PASoundness.PAtoCompactAddZeroGraphOutput.add_zero_output id u b q r hq hr hv
      · intro _hx b q r hq hr hv hg hd
        exact PASoundness.PAtoCompactRightZeroTermFunctional.functional id
          (guardFormula (allElimFormula φ x T)) hT b q r hv hg hd hq hr

theorem rightZero_allElim_certificate (φ : Peano.Formula) (x : Nat)
    {t : Peano.Term} (ht : RightZeroTerm t) :
    theoremCode (certificate (rightZero_allElim φ x ht)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

end PASoundness.PAtoCompactRightZeroAllElim

#print axioms PASoundness.PAtoCompactRightZeroAllElim.allElim_of_graph_laws
#print axioms PASoundness.PAtoCompactRightZeroAllElim.allElim_of_graph_laws_certificate
#print axioms PASoundness.PAtoCompactRightZeroAllElim.rightZero_allElim
#print axioms PASoundness.PAtoCompactRightZeroAllElim.rightZero_allElim_certificate
