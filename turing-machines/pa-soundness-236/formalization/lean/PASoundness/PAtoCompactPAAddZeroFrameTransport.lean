import PASoundness.PAtoCompactAddUnaryTotalityClosed
import PASoundness.PAtoCompactGuardedEqualityReflexivityUnary
import PASoundness.PAtoCompactFormulaTranslation

/-! Preserve one term value while transporting its graph to the actual
addition-child and equality-frame allocation bases. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddZeroFrameTransport
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactAddUnaryTotalityInduction
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousEqualityAlignment

/-- Rebase a graph to two bases while retaining the same output witness. -/
noncomputable def graph_to_two_bases (t : Peano.Term) (q b c d : Nat)
    (hqb : q < b) (hqc : q < c) (hqd : q < d)
    (htb : ∀ x ∈ t.varFinset, x < b)
    (htc : ∀ x ∈ t.varFinset, x < c)
    (htd : ∀ x ∈ t.varFinset, x < d) :
    KDerivation (imp (termGraph id t q b).encode
      (andF (termGraph id t q c) (termGraph id t q d)).encode) := by
  have hc := termGraph_base_transport id t b c q (by omega) (by omega)
    (by intro x hx; simpa only [id_eq] using htb x hx)
    (by intro x hx; simpa only [id_eq] using htc x hx)
  have hd := termGraph_base_transport id t b d q (by omega) (by omega)
    (by intro x hx; simpa only [id_eq] using htb x hx)
    (by intro x hx; simpa only [id_eq] using htd x hx)
  apply Context.closeEmpty
  apply Context.deduction
  let G := termGraph id t q b
  let Γ := [G.encode]
  have hG : Context Γ G.encode := .head [] _
  have hC : Context Γ (termGraph id t q c).encode := .mp hG (.closed hc.1)
  have hD : Context Γ (termGraph id t q d).encode := .mp hG (.closed hd.1)
  have h := Context.conjunctionIntro hC hD
  simpa [andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h

/-- A supplied guarded child-existence proof yields one common output at the
actual addition-child and equality-right allocation bases. -/
noncomputable def child_at_frame_bases_of_total (t : Peano.Term)
    (child : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (termGraph id t b (b+2)).encode))) :
    let a := Peano.add t Peano.zero
    let A := a.equal t
    let b := guardBase A
    KDerivation (imp (guardFormula A).encode
      (existsCode b (andF (termGraph id t b (b+2+64))
        (termGraph id t b (b+2+termCost a))).encode)) := by
  let a := Peano.add t Peano.zero
  let A := a.equal t
  let b := guardBase A
  have hcover : ∀ x ∈ t.varFinset, id x ∈ A.freeVarFinset := by
    intro x hx
    simp only [id_eq, A, eq_free, Finset.mem_union]
    exact Or.inr hx
  have hb : ∀ x ∈ t.varFinset, x < b := by
    intro x hx
    have h := free_lt_scopeBase A Fin.elim0 x (hcover x hx)
    simpa [b, guardBase, scopeBase] using h
  have htwo := graph_to_two_bases t b (b+2) (b+2+64) (b+2+termCost a)
    (by omega) (by omega) (by omega)
    (by intro x hx; have := hb x hx; omega)
    (by intro x hx; have := hb x hx; omega)
    (by intro x hx; have := hb x hx; omega)
  exact compose child (existsCongr b htwo)

/-- For the addition-unary term fragment, guarded child existence is supplied
by the already proved canonical totality theorem. -/
noncomputable def guarded_child_at_frame_bases (t : Peano.Term) (ht : AddUnaryTerm t) :
    let a := Peano.add t Peano.zero
    let A := a.equal t
    let b := guardBase A
    KDerivation (imp (guardFormula A).encode
      (existsCode b (andF (termGraph id t b (b+2+64))
        (termGraph id t b (b+2+termCost a))).encode)) := by
  let a := Peano.add t Peano.zero
  let A := a.equal t
  have hcover : ∀ x ∈ t.varFinset, id x ∈ A.freeVarFinset := by
    intro x hx
    simp only [id_eq, A, eq_free, Finset.mem_union]
    exact Or.inr hx
  have hc := PAtoCompactAddUnaryTotalityClosed.canonical_total id A ht hcover
  apply child_at_frame_bases_of_total t
  simpa [outputName, allocatorBase] using hc

#print axioms graph_to_two_bases
#print axioms child_at_frame_bases_of_total
#print axioms guarded_child_at_frame_bases
end PASoundness.PAtoCompactPAAddZeroFrameTransport
