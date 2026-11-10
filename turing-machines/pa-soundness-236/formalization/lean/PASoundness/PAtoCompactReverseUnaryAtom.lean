import PASoundness.PAtoCompactReverseTermAtomMatrix
import PASoundness.PAtoCompactReverseTermAtomFrame
import PASoundness.PAtoCompactReverseAtomBaseBridge
import PASoundness.PAtoCompactGeneralAtomFrameIntro

/-! Reverse substitution for an equality whose left term is a unary term,
while the right term is unchanged. A retained term graph and guard-to-domain
proofs for the unary term's variables are explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactReverseUnaryAtom
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactReverseTermAtomMatrix
open PASoundness.PAtoCompactReverseTermAtomFrame PASoundness.PAtoCompactReverseAtomBaseBridge
open PASoundness.PAtoCompactGeneralAtomFrameIntro PASoundness.PAtoCompactAllElimTermEqualityGeneral

/-- For a unary t and arbitrary unchanged s, a graph of t at q converts the
translated equality t=s into q=s. The guard supplies a candidate for every
variable occurring in t; q, and those variables, are below the graph base. -/
noncomputable def reverse_atomic (t s : Peano.Term) (ht : UnaryTerm t)
    (guard : Formula) (q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d)
    (hguard : ∀ a ∈ t.varFinset,
      KDerivation (imp guard.encode (domainAt d a).encode)) :
    KDerivation (imp guard.encode (imp (termGraph id t q d).encode
      (imp (code (t.equal s)) (code ((.var q : Peano.Term).equal s))))) := by
  let b := max (max q (guard.free.sup id)) (max (t.varFinset.sup id) (s.varFinset.sup id)) + 1
  have hqb : q < b := by dsimp [b]; omega
  have htb : ∀ a ∈ t.varFinset, a < b := by
    intro a ha
    have h : a ≤ t.varFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [b]; omega
  have hsb : ∀ a ∈ s.varFinset, a < b := by
    intro a ha
    have h : a ≤ s.varFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [b]; omega
  have hgb : ∀ a ∈ guard.free, a < b := by
    intro a ha
    have h : a ≤ guard.free.sup id := Finset.le_sup (f := id) ha
    dsimp [b]; omega
  have hdom : ∀ a ∈ t.varFinset,
      KDerivation (imp guard.encode (domainAt (b+2) a).encode) := by
    intro a ha
    have h := hguard a ha
    have htr := domainAt_transport d (b+2) a (by have := htd a ha; omega)
      (by have := htb a ha; omega)
    exact compose h htr
  let p := b+2
  let oldRight := b+2+termCost t
  let newRight := b+2+termCost (.var q : Peano.Term)
  let oldEq := oldRight+termCost s
  let newEq := newRight+termCost s
  have hm := reverse_matrix t s ht guard q b (b+1) p oldRight newRight oldEq newEq
    (by dsimp [p]; omega) (by dsimp [p]; omega)
    (by intro a ha; have := htb a ha; dsimp [p]; omega)
    (by intro a ha; have := hgb a ha; dsimp [p]; omega) hdom
    (by dsimp [oldRight]; omega) (by dsimp [newRight]; omega)
    (by intro a ha; have := hsb a ha; dsimp [oldRight]; omega)
    (by intro a ha; have := hsb a ha; dsimp [newRight]; omega)
    (by dsimp [oldEq, oldRight]; omega) (by dsimp [oldEq, oldRight]; omega)
    (by dsimp [newEq, newRight]; omega) (by dsimp [newEq, newRight]; omega)
    (by dsimp [newEq, newRight]; omega)
  have hi := target_frame_from_matrix (.var q : Peano.Term) s q b hqb
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hqb) hsb
  have hp : KDerivation (imp guard.encode (imp (termGraph id t q (b+2)).encode
      (imp (matrix id t s b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost s)).encode (equalityFrame id (.var q) s b).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let M := (matrix id t s b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost s)).encode
    let Γ := [M, (termGraph id t q (b+2)).encode, guard.encode]
    have hM : Context Γ M := Context.head _ _
    have hT : Context Γ (termGraph id t q (b+2)).encode := .hypothesis (by simp [Γ])
    have hG : Context Γ guard.encode := .hypothesis (by simp [Γ])
    have hmat := Context.mp hM (Context.mp hT (Context.mp hG (.closed hm)))
    exact .mp hmat (.closed hi)
  have hf := frame_of_pointwise guard t s q b hqb htb hgb hp
  exact reverse_atomic_of_frame t s q b d guard hqb htb hsb hqd htd hf

/-- For source atom x=s with x absent from s, the same result uses the actual
PA capture-avoiding substitution syntax on both sides. -/
noncomputable def reverse_atomic_substitution (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (guard : Formula) (q d : Nat) (hx : x ∉ s.varFinset)
    (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d)
    (hguard : ∀ a ∈ t.varFinset,
      KDerivation (imp guard.encode (domainAt d a).encode)) :
    KDerivation (imp guard.encode (imp (termGraph id t q d).encode
      (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x t))
        (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q)))))) := by
  simpa only [atom_subst_fresh_right s t x hx, atom_subst_fresh_right s (.var q) x hx] using
    reverse_atomic t s ht guard q d hqd htd hguard

theorem reverse_atomic_substitution_certificate (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (guard : Formula) (q d : Nat) (hx : x ∉ s.varFinset)
    (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d)
    (hguard : ∀ a ∈ t.varFinset,
      KDerivation (imp guard.encode (domainAt d a).encode)) :
    theoremCode (certificate (reverse_atomic_substitution x t s ht guard q d hx hqd htd hguard)) =
      imp guard.encode (imp (termGraph id t q d).encode
        (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x t))
          (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q))))) := certificate_correct _

end PASoundness.PAtoCompactReverseUnaryAtom

#print axioms PASoundness.PAtoCompactReverseUnaryAtom.reverse_atomic
#print axioms PASoundness.PAtoCompactReverseUnaryAtom.reverse_atomic_substitution
#print axioms PASoundness.PAtoCompactReverseUnaryAtom.reverse_atomic_substitution_certificate
