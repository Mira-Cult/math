import PASoundness.PAtoCompactAllElimTermEquality
import PASoundness.PAtoCompactGuardedPropositional
import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactZeroBaseTransport

/-! Conditional finite-K construction of the PA successor-not-zero leaf.
The only missing input is the displayed allocated relation incompatibility.
No graph-existence, PA soundness or K soundness premise is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccNeZeroAxiomConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedPropositional
open PASoundness.PAtoCompactPropositionalHandlers PASoundness.PAtoCompactAllElimTermEquality
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactZeroBaseTransport

/-- Refute the actual successor-equality matrix from an explicit proof that
the allocated successor and zero values cannot be equivalent. -/
noncomputable def matrix_refutation (t : Peano.Term) (b : Nat)
    (bad : KDerivation (imp (succAt (b+2) (b+2) b).encode
      (imp (zeroAt (b+2+termCost (Peano.succ t)) (b+1)).encode
        (imp (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1)).encode 1)))) :
    KDerivation (imp (matrix id (Peano.succ t) Peano.zero b (b+1) (b+2)
      (b+2+termCost (Peano.succ t))
      (b+2+termCost (Peano.succ t)+termCost Peano.zero)).encode 1) := by
  let S := (succAt (b+2) (b+2) b).encode
  let Z := (zeroAt (b+2+termCost (Peano.succ t)) (b+1)).encode
  let E := (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1)).encode
  let C := (termGraph id t (b+2) (b+2+64)).encode
  let G := (termGraph id (Peano.succ t) b (b+2)).encode
  let H := (termGraph id Peano.zero (b+1) (b+2+termCost (Peano.succ t))).encode
  let M := (matrix id (Peano.succ t) Peano.zero b (b+1) (b+2)
    (b+2+termCost (Peano.succ t))
    (b+2+termCost (Peano.succ t)+termCost Peano.zero)).encode
  let N := andF (termGraph id Peano.zero (b+1) (b+2+termCost (Peano.succ t)))
    (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1))
  have nf : b+2 ∉ N.free := by
    intro hn
    simp only [N, andF_free, Finset.mem_union] at hn
    rcases hn with h | h
    · have hh := termGraph_free_subset id Peano.zero (b+1) (b+2+termCost (Peano.succ t)) h
      simp [Peano.zero, Term.varFinset] at hh
    · have hh := equivAt_free (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1) h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      omega
  have hpoint : KDerivation (imp (both H E) (imp (both C S) 1)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both C S, both H E]
    have hcs : Context Γ (both C S) := .head _ _
    have hm : Context Γ (both H E) := .hypothesis (by simp [Γ])
    have hh : Context Γ H := Context.conjunctionLeft hm
    have he : Context Γ E := Context.conjunctionRight hm
    have hz : Context Γ Z := by
      have hh' : Context Γ (both (domainAt (b+2+termCost (Peano.succ t)) (b+1)).encode Z) := by
        simpa [H, Z, Peano.zero, termGraph, andF, CompactNamed.Formula.not,
          CompactNamed.Formula.encode, both, neg] using hh
      exact Context.conjunctionRight hh'
    have hs : Context Γ S := Context.conjunctionRight hcs
    exact .mp he (.mp hz (.mp hs (.closed bad)))
  have vN : KDerivation (imp (both H E) (allCode (b+2) (both H E))) := by
    simpa [N, H, E, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg]
      using free_vacuity (b+2) N nf
  have hElim := exists_left_guarded (b+2) (both H E) (both C S) 1 vN
    (explosion (allCode (b+2) 1)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [M]
  have hm : Context Γ (both G (both H E)) := by
    simpa [Γ, M, G, H, E, matrix, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using (Context.head [] M)
  have hg : Context Γ G := Context.conjunctionLeft hm
  have hex : Context Γ (existsCode (b+2) (both C S)) := by
    have hg' : Context Γ (both (domainAt (b+2) b).encode (existsCode (b+2) (both C S))) := by
      simpa [G, C, S, Peano.succ, termGraph, andF, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, both, neg] using hg
    exact Context.conjunctionRight hg'
  exact .mp hex (.mp (Context.conjunctionRight hm) (.closed hElim))

/-- Eliminate the actual two equality-value witnesses. Bottom is vacuous for
each witness; no existence or functionality of the argument graph is used. -/
noncomputable def frame_refutation (t : Peano.Term) (b : Nat)
    (bad : KDerivation (imp (succAt (b+2) (b+2) b).encode
      (imp (zeroAt (b+2+termCost (Peano.succ t)) (b+1)).encode
        (imp (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1)).encode 1)))) :
    KDerivation (imp (equalityFrame id (Peano.succ t) Peano.zero b).encode 1) := by
  let M := (matrix id (Peano.succ t) Peano.zero b (b+1) (b+2)
    (b+2+termCost (Peano.succ t))
    (b+2+termCost (Peano.succ t)+termCost Peano.zero)).encode
  have point : KDerivation (imp M 1) := matrix_refutation t b bad
  have inner : KDerivation (imp (existsCode (b+1) M) 1) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (explosion (allCode (b+1) 1))
      (.closed (.generalize (b+1) point)) (.head [] _)
  have outer : KDerivation (imp (existsCode b (existsCode (b+1) M)) 1) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (explosion (allCode b 1))
      (.closed (.generalize b inner)) (.head [] _)
  simpa [M, equalityFrame, matrix, andF, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, both, neg] using outer

/-- A proof of the displayed allocated relation incompatibility suffices for
the actual guarded PA successor-not-zero axiom for arbitrary argument t. -/
noncomputable def succ_ne_zero_of_incompatibility (t : Peano.Term)
    (bad : let b := scopeBase ((Peano.succ t).equal Peano.zero) Fin.elim0
      KDerivation (imp (succAt (b+2) (b+2) b).encode
        (imp (zeroAt (b+2+termCost (Peano.succ t)) (b+1)).encode
          (imp (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1)).encode 1)))) :
    KDerivation (guardedCode ((Peano.succ t).equal Peano.zero).not) := by
  apply guardedOfUnconditional
  rw [code_not]
  change KDerivation (imp (code ((Peano.succ t).equal Peano.zero)) 1)
  unfold code
  rw [original_shape]
  exact frame_refutation t _ bad

theorem succ_ne_zero_of_incompatibility_certificate (t : Peano.Term)
    (bad : let b := scopeBase ((Peano.succ t).equal Peano.zero) Fin.elim0
      KDerivation (imp (succAt (b+2) (b+2) b).encode
        (imp (zeroAt (b+2+termCost (Peano.succ t)) (b+1)).encode
          (imp (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1)).encode 1)))) :
    theoremCode (certificate (succ_ne_zero_of_incompatibility t bad)) =
      guardedCode ((Peano.succ t).equal Peano.zero).not := certificate_correct _

/-- Rebase successor and zero relations into the equality relation's private
block. All three witnesses keep their literal names; no injectivity or
distinctness assumption on denoted objects is made. -/
noncomputable def allocated_incompatibility (t : Peano.Term) (b : Nat)
    (bad : let e := b+2+termCost (Peano.succ t)+termCost Peano.zero
      KDerivation (imp (succAt e (b+2) b).encode
        (imp (zeroAt e (b+1)).encode (imp (equivAt e b (b+1)).encode 1)))) :
    KDerivation (imp (succAt (b+2) (b+2) b).encode
      (imp (zeroAt (b+2+termCost (Peano.succ t)) (b+1)).encode
        (imp (equivAt (b+2+termCost (Peano.succ t)+termCost Peano.zero) b (b+1)).encode 1))) := by
  let s := b+2+termCost (Peano.succ t)
  let e := s+termCost Peano.zero
  have hcost := termCost_ge_block (Peano.succ t)
  have hzero := termCost_ge_block Peano.zero
  have hs := (succAt_base_alpha (b+2) e (b+2) b
    (by omega) (by omega) (by dsimp [e, s]; omega) (by dsimp [e, s]; omega)).forward
  have hz := zeroAt_base_forward s e (b+1) (by dsimp [s]; omega) (by dsimp [e, s]; omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt e b (b+1)).encode, (zeroAt s (b+1)).encode,
    (succAt (b+2) (b+2) b).encode]
  have he : Context Γ (equivAt e b (b+1)).encode := .head _ _
  have hz' : Context Γ (zeroAt e (b+1)).encode :=
    .mp (.hypothesis (by simp [Γ])) (.closed hz)
  have hs' : Context Γ (succAt e (b+2) b).encode :=
    .mp (.hypothesis (by simp [Γ])) (.closed hs)
  exact .mp he (.mp hz' (.mp hs' (.closed bad)))

/-- The actual guarded PA axiom follows from the single same-base relation
incompatibility shown here. This is a finite K proof transformer. -/
noncomputable def succ_ne_zero_of_same_base (t : Peano.Term)
    (bad : let b := scopeBase ((Peano.succ t).equal Peano.zero) Fin.elim0
      let e := b+2+termCost (Peano.succ t)+termCost Peano.zero
      KDerivation (imp (succAt e (b+2) b).encode
        (imp (zeroAt e (b+1)).encode (imp (equivAt e b (b+1)).encode 1)))) :
    KDerivation (guardedCode ((Peano.succ t).equal Peano.zero).not) :=
  succ_ne_zero_of_incompatibility t (allocated_incompatibility t _ bad)

theorem succ_ne_zero_of_same_base_certificate (t : Peano.Term)
    (bad : let b := scopeBase ((Peano.succ t).equal Peano.zero) Fin.elim0
      let e := b+2+termCost (Peano.succ t)+termCost Peano.zero
      KDerivation (imp (succAt e (b+2) b).encode
        (imp (zeroAt e (b+1)).encode (imp (equivAt e b (b+1)).encode 1)))) :
    theoremCode (certificate (succ_ne_zero_of_same_base t bad)) =
      guardedCode ((Peano.succ t).equal Peano.zero).not := certificate_correct _

end PASoundness.PAtoCompactSuccNeZeroAxiomConditional

#print axioms PASoundness.PAtoCompactSuccNeZeroAxiomConditional.succ_ne_zero_of_incompatibility
#print axioms PASoundness.PAtoCompactSuccNeZeroAxiomConditional.succ_ne_zero_of_incompatibility_certificate
#print axioms PASoundness.PAtoCompactSuccNeZeroAxiomConditional.succ_ne_zero_of_same_base
