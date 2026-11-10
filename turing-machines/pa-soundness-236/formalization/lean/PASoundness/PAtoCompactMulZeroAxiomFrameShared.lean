import PASoundness.PAtoCompactAllElimTermEquality
import PASoundness.PAtoCompactCandidateDynamicReflexivity
import PASoundness.PAtoCompactGuardedEqualityReflexivityUnary
import PASoundness.PAtoCompactZeroBaseTransport

/-! Capture-safe equality-frame introduction from a common value witness.
This constructs finite K proof data and assumes no graph functionality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulZeroAxiomFrameShared

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactCandidateDynamicReflexivity
open PASoundness.PAtoCompactGuardedEqualityReflexivityUnary
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactZeroBaseTransport

/-- Introduce the two equality witnesses using one existing graph value. -/
def frame_from_shared_matrix (t u : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hu : ∀ a ∈ u.varFinset, a < b) :
    KDerivation (imp (matrix id t u q q (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost u)).encode (equalityFrame id t u b).encode) := by
  let p := b+2
  let s := b+2+termCost t
  let e := b+2+termCost t+termCost u
  let N := matrix id t u b (b+1) p s e
  let M := matrix id t u q q p s e
  have hb : b ∉ N.binders := matrix_below_not_binder id t u b (b+1) p s e b
    (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
  have hb1 : b+1 ∉ N.binders := matrix_below_not_binder id t u b (b+1) p s e (b+1)
    (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
  have hqb : q ∉ N.binders := matrix_below_not_binder id t u b (b+1) p s e q
    (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
  have hrep : replace (b+1) q (replace b q N) = M := by
    dsimp [N, M]
    exact matrix_replace_two_witnesses id t u b (b+1) q q p s e
      (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
      (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
      (by intro a ha; have := hu a ha; simp only [id_eq]; omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
      (by intro a ha; have := hu a ha; simp only [id_eq]; omega)
      (by omega) (by omega)
  have hi := exists_from_instance (b+1) q (replace b q N) (by omega)
    (by simpa only [replace_binders] using hb1)
    (by simpa only [replace_binders] using hqb)
  rw [hrep] at hi
  have ho := exists_from_instance b q (.ex (b+1) N) (by omega)
    (by simpa [Formula.binders, show b ≠ b+1 by omega] using hb)
    (by simpa [Formula.binders, show q ≠ b+1 by omega] using hqb)
  change KDerivation (imp (existsCode (b+1) (replace b q N).encode)
    (equalityFrame id t u b).encode) at ho
  exact compose hi ho

theorem frame_from_shared_matrix_certificate (t u : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hu : ∀ a ∈ u.varFinset, a < b) :
    theoremCode (certificate (frame_from_shared_matrix t u q b hq ht hu)) =
      imp (matrix id t u q q (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost u)).encode (equalityFrame id t u b).encode :=
  certificate_correct _

/-- A common outer witness supplies both value graphs and its own quotient
reflexivity, so only the second existential must be introduced. -/
noncomputable def shared_graphs_to_inner (t u : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b) :
    KDerivation (imp (andF (termGraph id t b (b+2))
      (termGraph id u b (b+2+termCost t))).encode
      (existsCode (b+1) (matrix id t u b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost u)).encode)) := by
  let e := b+2+termCost t+termCost u
  let M := matrix id t u b (b+1) (b+2) (b+2+termCost t) e
  have hbb : b ∉ M.binders := matrix_below_not_binder id t u b (b+1) (b+2)
    (b+2+termCost t) e b (by omega) (by omega) (by dsimp [e]; omega)
  have hb1 : b+1 ∉ M.binders := matrix_below_not_binder id t u b (b+1) (b+2)
    (b+2+termCost t) e (b+1) (by omega) (by omega) (by dsimp [e]; omega)
  have hrepl : replace (b+1) b M = matrix id t u b b (b+2) (b+2+termCost t) e := by
    dsimp [M]
    rw [matrix_replace_fresh_source id t u b (b+1) (b+2) (b+2+termCost t) e
      (b+1) b (by omega) (by omega) (by dsimp [e]; omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
      (by intro a ha; have := hu a ha; simp only [id_eq]; omega)]
    simp [rename]
  have hi := exists_from_instance (b+1) b M (by omega) hb1 hbb
  rw [hrepl] at hi
  have hd := compose (termGraph_domain id t b (b+2))
    (domainAt_transport (b+2) e b (by omega) (by dsimp [e]; omega))
  have he := compose hd (dynamic_reflexive e b (by dsimp [e]; omega))
  apply Context.closeEmpty
  apply Context.deduction
  let G := andF (termGraph id t b (b+2)) (termGraph id u b (b+2+termCost t))
  let Γ := [G.encode]
  have hG : Context Γ (both (termGraph id t b (b+2)).encode
      (termGraph id u b (b+2+termCost t)).encode) := by
    simpa [Γ, G, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using (Context.head [] G.encode)
  have h1 := Context.conjunctionLeft hG
  have h2 := Context.conjunctionRight hG
  have hE : Context Γ (equivAt e b b).encode := .mp h1 (.closed he)
  have hm := Context.conjunctionIntro h1 (Context.conjunctionIntro h2 hE)
  have hm' : Context Γ (matrix id t u b b (b+2) (b+2+termCost t) e).encode := by
    simpa [matrix, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hm
  exact .mp hm' (.closed hi)

/-- A jointly existing value of two term graphs proves their translated
equality; the proof reuses one witness and needs no functionality hypothesis. -/
noncomputable def shared_graphs_to_frame (t u : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b) :
    KDerivation (imp (existsCode b (andF (termGraph id t b (b+2))
      (termGraph id u b (b+2+termCost t))).encode)
      (equalityFrame id t u b).encode) := by
  have h := existsCongr b (shared_graphs_to_inner t u b ht hu)
  simpa [equalityFrame, matrix, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h

theorem shared_graphs_to_frame_certificate (t u : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b) :
    theoremCode (certificate (shared_graphs_to_frame t u b ht hu)) =
      imp (existsCode b (andF (termGraph id t b (b+2))
        (termGraph id u b (b+2+termCost t))).encode) (equalityFrame id t u b).encode :=
  certificate_correct _

/-- A term graph with an output that also satisfies zero supplies both
equality graphs at the actual distinct frame allocation bases. -/
noncomputable def shared_zero_to_frame (t : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) :
    KDerivation (imp (existsCode b (andF (termGraph id t b (b+2))
      (zeroAt (b+2) b)).encode) (equalityFrame id t Peano.zero b).encode) := by
  let p := b+2
  let s := b+2+termCost t
  let G := termGraph id t b p
  let Z := zeroAt p b
  let V := termGraph id Peano.zero b s
  let A := andF G Z
  let B := andF G V
  have hdom := compose (termGraph_domain id t b p)
    (domainAt_transport p s b (by dsimp [p]; omega) (by dsimp [s]; omega))
  have hz := zeroAt_base_forward p s b (by dsimp [p]; omega) (by dsimp [s]; omega)
  have point : KDerivation (imp A.encode B.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [A.encode]
    have ha : Context Γ (both G.encode Z.encode) := by
      simpa [Γ, A, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using (Context.head [] A.encode)
    have hg := Context.conjunctionLeft ha
    have hzero := Context.conjunctionRight ha
    have hdom' : Context Γ (domainAt s b).encode := .mp hg (.closed hdom)
    have hz' : Context Γ (zeroAt s b).encode := .mp hzero (.closed hz)
    have hv : Context Γ V.encode := by
      have hh := Context.conjunctionIntro hdom' hz'
      simpa [V, Peano.zero, termGraph, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
    have hh := Context.conjunctionIntro hg hv
    simpa [B, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
  have hpack := existsCongr b point
  have hf := shared_graphs_to_frame t Peano.zero b ht (by simp [Peano.zero, Term.varFinset])
  exact compose hpack hf

theorem shared_zero_to_frame_certificate (t : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) :
    theoremCode (certificate (shared_zero_to_frame t b ht)) =
      imp (existsCode b (andF (termGraph id t b (b+2))
        (zeroAt (b+2) b)).encode) (equalityFrame id t Peano.zero b).encode :=
  certificate_correct _

#print axioms frame_from_shared_matrix
#print axioms shared_graphs_to_frame
#print axioms shared_zero_to_frame
end PASoundness.PAtoCompactMulZeroAxiomFrameShared
