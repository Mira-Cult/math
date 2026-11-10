import PASoundness.PAtoCompactAllElimTermEqualityGeneral

/-! Reverse atomic substitution: transport a supplied finite-K common-base
frame implication to the literal formula allocation bases. The common-base
frame implication remains an explicit proof input. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactReverseAtomBaseBridge
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactAllElimTermEqualityGeneral
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactFreeNames

/-- A finite-K reverse implication at an intermediate equality-frame base
transports to the actual translated PA equality codes. No graph functionality
is claimed by this constructor: the intermediate proof is an explicit input. -/
noncomputable def reverse_atomic_of_frame (t s : Peano.Term) (q b d : Nat)
    (g : CompactNamed.Formula)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hs : ∀ a ∈ s.varFinset, a < b) (hqd : q < d)
    (htd : ∀ a ∈ t.varFinset, a < d)
    (frame : KDerivation (imp g.encode
      (imp (termGraph id t q (b+2)).encode
        (imp (equalityFrame id t s b).encode
          (equalityFrame id (.var q) s b).encode)))) :
    KDerivation (imp g.encode (imp (termGraph id t q d).encode
      (imp (code (t.equal s)) (code ((.var q : Peano.Term).equal s))))) := by
  let S := t.equal s
  let T := ((.var q : Peano.Term).equal s)
  let sb := scopeBase S Fin.elim0
  let tb := scopeBase T Fin.elim0
  have htS : ∀ a ∈ t.varFinset, a < sb := by
    intro a ha
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, ha]
  have hsS : ∀ a ∈ s.varFinset, a < sb := by
    intro a ha
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, ha]
  have hqT : q < tb := by
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, Term.varFinset]
  have hsT : ∀ a ∈ s.varFinset, a < tb := by
    intro a ha
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, ha]
  have hg := (termGraph_base_transport id t d (b+2) q hqd (by omega)
    (by intro a ha; simpa using htd a ha) (by intro a ha; simp only [id_eq]; have := ht a ha; omega)).1
  have hs' := (equalityFrame_base_transport id t s sb b
    (by intro a ha; simpa using htS a ha)
    (by intro a ha; simpa using hsS a ha)
    (by intro a ha; simpa using ht a ha)
    (by intro a ha; simpa using hs a ha)).1
  have ht' := (equalityFrame_base_transport id (.var q : Peano.Term) s b tb
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hq)
    (by intro a ha; simpa using hs a ha)
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hqT)
    (by intro a ha; simpa using hsT a ha)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [code S, (termGraph id t q d).encode, g.encode]
  have hG : Context Γ (termGraph id t q d).encode := .hypothesis (by simp [Γ])
  have hS : Context Γ (code S) := Context.head _ _
  have hguard : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hSb : Context Γ (equalityFrame id t s b).encode := by
    apply Context.mp _ (.closed hs')
    simpa only [code, original_shape, S, sb] using hS
  have hTb := Context.mp hSb (Context.mp (Context.mp hG (.closed hg)) (Context.mp hguard (.closed frame)))
  have hT := Context.mp hTb (.closed ht')
  simpa only [Γ, code, original_shape, S, T, tb] using hT

theorem reverse_atomic_of_frame_certificate (t s : Peano.Term) (q b d : Nat)
    (g : CompactNamed.Formula)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hs : ∀ a ∈ s.varFinset, a < b) (hqd : q < d)
    (htd : ∀ a ∈ t.varFinset, a < d)
    (frame : KDerivation (imp g.encode
      (imp (termGraph id t q (b+2)).encode
        (imp (equalityFrame id t s b).encode
          (equalityFrame id (.var q) s b).encode)))) :
    theoremCode (certificate (reverse_atomic_of_frame t s q b d g hq ht hs hqd htd frame)) =
      imp g.encode (imp (termGraph id t q d).encode
        (imp (code (t.equal s)) (code ((.var q : Peano.Term).equal s)))) := certificate_correct _
end PASoundness.PAtoCompactReverseAtomBaseBridge

#print axioms PASoundness.PAtoCompactReverseAtomBaseBridge.reverse_atomic_of_frame
#print axioms PASoundness.PAtoCompactReverseAtomBaseBridge.reverse_atomic_of_frame_certificate
