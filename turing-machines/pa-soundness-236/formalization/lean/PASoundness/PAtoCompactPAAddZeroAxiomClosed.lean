import PASoundness.PAtoCompactPAAddZeroAxiomConditional
import PASoundness.PAtoCompactPAAddZeroGraphFromChild

/-! Finite K proof of guarded PA addition by zero, conditional only on child
term-graph existence; canonical totality discharges it for addition-unary terms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddZeroAxiomClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactAddUnaryTotalityInduction PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactPAAddZeroAxiomConditional PASoundness.PAtoCompactPAAddZeroGraphFromChild

/-- Same-output graph construction at the exact equality-frame allocator. -/
noncomputable def graph_step (t : Peano.Term) :
    let a := Peano.add t Peano.zero
    let A := a.equal t
    let b := guardBase A
    KDerivation (imp (termGraph id t b (b+2+64)).encode
      (termGraph id a b (b+2)).encode) := by
  let a := Peano.add t Peano.zero
  let A := a.equal t
  let b := guardBase A
  have hnames : ∀ z ∈ t.varFinset, id z < b+2 := by
    intro z hz
    have hf : z ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inr hz
    have hh := free_lt_scopeBase A Fin.elim0 z hf
    simp only [id_eq]
    simp [b, guardBase, scopeBase] at hh ⊢
    omega
  have h := add_zero_from_child id t (b+2) b (by omega) hnames
  simpa [a, A, b, Peano.add, Peano.zero, binaryTerm] using h

/-- The actual guarded PA axiom for arbitrary t, from explicit guarded
existence of its child graph at the canonical frame names. -/
noncomputable def add_zero_of_child (t : Peano.Term)
    (child : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (termGraph id t b (b+2)).encode))) :
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) :=
  add_zero_of_child_and_step t child (graph_step t)

/-- The actual guarded PA axiom for all terms built from variables, zero,
successor and addition, with no supplied K proof. -/
noncomputable def add_zero (t : Peano.Term) (ht : AddUnaryTerm t) :
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) :=
  add_zero_addUnary_of_step t ht (graph_step t)

theorem add_zero_certificate (t : Peano.Term) (ht : AddUnaryTerm t) :
    theoremCode (certificate (add_zero t ht)) =
      guardedCode ((Peano.add t Peano.zero).equal t) := certificate_correct _

#print axioms graph_step
#print axioms add_zero_of_child
#print axioms add_zero
#print axioms add_zero_certificate
end PASoundness.PAtoCompactPAAddZeroAxiomClosed
