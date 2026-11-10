import PASoundness.PAtoCompactAllElimVariable
import PASoundness.PAtoCompactAllElimVariableFull
import PASoundness.PAtoCompactSuccTermTotality

/-! Universal elimination reduced to K compatibility between a variable
instance and exact source substitution under a term graph. For unary terms
the guarded graph existence input is constructed; for general terms it
remains explicit. All inputs are only needed in the occurrence branch. -/
namespace PASoundness.PAtoCompactUnarySubstitutionReduce

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactAllElimVariable PASoundness.PAtoCompactAllElimVariableFull
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactSuccTermTotality

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Construct guarded elimination from per-instance term-graph existence and
variable-to-term substitution compatibility. Both proofs are needed only
when x actually occurs, avoiding a false uniform graph-existence premise. -/
noncomputable def allElim_of_variable_graph (φ : Peano.Formula) (x : Nat)
    (t : Peano.Term)
    (totality : x ∈ φ.freeVarFinset →
      KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
        (existsCode (outputName (allElimFormula φ x t))
          (termGraph id t (outputName (allElimFormula φ x t))
            (allocatorBase (allElimFormula φ x t))).encode)))
    (compatibility : x ∈ φ.freeVarFinset →
      KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
        (imp (termGraph id t (outputName (allElimFormula φ x t))
          (allocatorBase (allElimFormula φ x t))).encode
          (imp (code (FOL.substAt φ x (.var (outputName (allElimFormula φ x t)))))
            (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  by_cases hx : x ∈ φ.freeVarFinset
  · let A := allElimFormula φ x t
    let q := outputName A
    let b := allocatorBase A
    let G := (guardFormula A).encode
    let U := code (FOL.allAt x φ)
    let T := code (FOL.substAt φ x t)
    let V := code (FOL.substAt φ x (.var q))
    let R := termGraph id t q b
    let z := instanceBinder φ x q
    have htotal : KDerivation (imp G (existsCode q R.encode)) :=
      totality hx
    have hvG : KDerivation (imp G (allCode q G)) :=
      free_vacuity q _ (outputName_guard_fresh φ x t)
    have hvU : KDerivation (imp U (allCode q U)) :=
      free_vacuity q _ (outputName_all_fresh φ x t)
    have hvT : KDerivation (imp T (allCode q T)) :=
      free_vacuity q _ (outputName_target_fresh φ x t)
    have hqz : q < z := by dsimp [z, instanceBinder]; omega
    have hqb : q < b + 32 := by dsimp [b, allocatorBase]; omega
    have hdom : KDerivation (imp R.encode (domainAt (z+1) q).encode) :=
      PASoundness.CompactDerivations.compose (termGraph_domain id t q b)
        (domainAt_transport b (z+1) q hqb (by omega))
    have hv : KDerivation (imp U (imp (domainAt (z+1) q).encode V)) :=
      variable_instance φ x q
    change KDerivation (imp G (imp U T))
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [U, G]
    have hg : Context Γ G := .hypothesis (by simp [Γ])
    apply Context.existsElim hvT
    · apply Context.generalize q
      · intro h hh
        by_cases he : h = U
        · subst h
          exact hvU
        · have hg : h = G := by simpa [Γ, he] using hh
          subst h
          exact hvG
      · apply Context.deduction
        let Δ := [R.encode, U, G]
        have hr : Context Δ R.encode := Context.head [U, G] _
        have hu : Context Δ U := .hypothesis (by simp [Δ])
        have hg : Context Δ G := .hypothesis (by simp [Δ])
        have hd : Context Δ (domainAt (z+1) q).encode := .mp hr (.closed hdom)
        have hv' : Context Δ V := .mp hd (.mp hu (.closed hv))
        exact .mp hv' (.mp hr (.mp hg (.closed (compatibility hx))))
    · exact .mp hg (.closed htotal)
  · exact PASoundness.PAtoCompactVacuousAllElim.allElim_of_unused φ x t hx

/-- For a unary term, guarded graph existence is constructed from the
actual axiom guard; only K substitution compatibility remains. -/
noncomputable def unary_allElim_of_variable_graph (φ : Peano.Formula) (x : Nat)
    (t : Peano.Term) (ht : UnaryTerm t)
    (compatibility : x ∈ φ.freeVarFinset →
      KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
        (imp (termGraph id t (outputName (allElimFormula φ x t))
          (allocatorBase (allElimFormula φ x t))).encode
          (imp (code (FOL.substAt φ x (.var (outputName (allElimFormula φ x t)))))
            (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  apply allElim_of_variable_graph φ x t
  · intro hx
    apply PAtoCompactUnaryGuardedCanonical.unary_total id (allElimFormula φ x t) ht
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hx ha
  · exact compatibility

theorem unary_allElim_of_variable_graph_certificate (φ : Peano.Formula) (x : Nat)
    (t : Peano.Term) (ht : UnaryTerm t)
    (compatibility : x ∈ φ.freeVarFinset →
      KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
        (imp (termGraph id t (outputName (allElimFormula φ x t))
          (allocatorBase (allElimFormula φ x t))).encode
          (imp (code (FOL.substAt φ x (.var (outputName (allElimFormula φ x t)))))
            (code (FOL.substAt φ x t)))))) :
    theoremCode (certificate (unary_allElim_of_variable_graph φ x t ht compatibility)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

end PASoundness.PAtoCompactUnarySubstitutionReduce

#print axioms PASoundness.PAtoCompactUnarySubstitutionReduce.unary_allElim_of_variable_graph
#print axioms PASoundness.PAtoCompactUnarySubstitutionReduce.allElim_of_variable_graph
#print axioms PASoundness.PAtoCompactUnarySubstitutionReduce.unary_allElim_of_variable_graph_certificate
