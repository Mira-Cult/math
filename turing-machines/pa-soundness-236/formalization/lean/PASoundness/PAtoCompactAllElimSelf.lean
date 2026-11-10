import PASoundness.PAtoCompactDirectGeneralization
import PASoundness.PAtoCompactGuardedAllElim
import PASoundness.PAtoCompactVacuousAllElim

/-! A finite K proof of the genuine PA universal-elimination axiom when the
substitution term is the same variable as the one quantified. -/
namespace PASoundness.PAtoCompactAllElimSelf

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactScopedActiveAll
open PASoundness.PAtoCompactGeneralizationConditional
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactGeneralizationGuardAssembly PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactGuardedAllElim

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Rebind the translated PA universal at the original source name. The
common fresh name in the proof avoids capture even under nested quantifiers. -/
noncomputable def allAt_align_self (φ : Peano.Formula) (x : Nat) :
    KBoth (rawGuard x (scopeAt φ x x)) (formula (FOL.allAt x φ)) := by
  let z := topName x φ
  let w := commonFresh φ x
  let B := allAtBody x φ
  let Tx := scopeAt φ x x
  let Tz := scopeAt φ x z
  let Tw := scopeAt φ x w
  have hxw : x < w := by dsimp [w, commonFresh]; omega
  have hzw : z < w := by dsimp [w, z, commonFresh]; omega
  have hwTx : w ∉ Tx.names := by
    intro hh
    have hl : w ≤ (Tx.names ∪ Tz.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_left _ hh)
    dsimp [w, commonFresh, Tx, Tz, z] at hl
    omega
  have hwTz : w ∉ Tz.names := by
    intro hh
    have hl : w ≤ (Tx.names ∪ Tz.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_right _ hh)
    dsimp [w, commonFresh, Tx, Tz, z] at hl
    omega
  have hxfree : x ∉ B.freeVarFinset := by
    change x ∉ (FOL.allAt x φ).freeVarFinset
    simp [PASoundness.SyntaxTransport.allAt_freeVars]
  have hzfree : z ∉ B.freeVarFinset := by
    change z ∉ (FOL.allAt x φ).freeVarFinset
    exact topName_not_universal_free φ x
  have envx : (rename x w ∘ Fin.snoc Fin.elim0 x) = Fin.snoc Fin.elim0 w := by
    funext i
    fin_cases i
    simp [rename]
  have envz : (rename z w ∘ Fin.snoc Fin.elim0 z) = Fin.snoc Fin.elim0 w := by
    funext i
    fin_cases i
    simp [rename]
  have p1 := scoped_active_replace B (Fin.snoc Fin.elim0 x) (Fin.last 0) w
    (by simpa using hxfree) (by simpa using hxw) (by simpa [Tx, scopeAt] using hwTx)
  have p2 := scoped_active_replace B (Fin.snoc Fin.elim0 z) (Fin.last 0) w
    (by simpa using hzfree) (by simpa using hzw) (by simpa [Tz, scopeAt] using hwTz)
  have pair1 : KBoth (replace x w Tx) Tw := by simpa [Tx, Tw, scopeAt, envx] using p1
  have pair2 : KBoth (replace z w Tz) Tw := by simpa [Tz, Tw, scopeAt, envz] using p2
  have hc : KBoth (replace x w Tx) (replace z w Tz) :=
    ⟨compose pair1.1 pair2.2, compose pair2.1 pair1.2⟩
  have hxb : x ∉ Tx.binders := by
    have hh := active_not_binder B (Fin.snoc Fin.elim0 x) (Fin.last 0)
    simpa [Tx, scopeAt] using hh
  have hzb : z ∉ Tz.binders := by
    have hh := active_not_binder B (Fin.snoc Fin.elim0 z) (Fin.last 0)
    simpa [Tz, scopeAt] using hh
  have ha := raw_align x z w (w+1) Tx Tz hxw hzw (by omega) hxb hzb hwTx hwTz hc
  change KBoth (rawGuard x Tx) (rawGuard z Tz)
  exact ha

/-- Under a candidate guard for x, the translated universal yields the
translation of its own source body. -/
noncomputable def self_instance (φ : Peano.Formula) (x : Nat) :
    KDerivation (imp (code (FOL.allAt x φ))
      (imp (domainAt (x+1) x).encode (code φ))) := by
  let T := scopeAt φ x x
  let M : Formula := .imp (domainAt (x+1) x) T
  have hb : x ∉ M.binders := by
    simp only [M, Formula.binders, Finset.mem_union, not_or]
    constructor
    · intro h
      have hh := PASoundness.PAtoCompactTermGraphBinderRange.domainAt_private (x+1) x x h
      omega
    · have hh := active_not_binder (allAtBody x φ) (Fin.snoc Fin.elim0 x) (Fin.last 0)
      simpa [T, scopeAt] using hh
  have hi := CompactNamed.allSpecialize x M hb
  have halign := (actualBindSelf.align φ x).2
  have hbody := implicationCongr (identity (domainAt (x+1) x).encode) halign
  have hs := compose (allAt_align_self φ x).2 (compose hi hbody)
  simpa [rawGuard, M, T, code, Formula.encode] using hs

/-- Every self-variable PA universal-elimination axiom has a finite guarded
K derivation. The unused-variable case needs no candidate for the variable. -/
noncomputable def allElim_self (φ : Peano.Formula) (x : Nat) :
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x (.var x)))) := by
  by_cases hx : x ∈ φ.freeVarFinset
  · let A := allElimFormula φ x (.var x)
    have hmem : x ∈ ((.var x : Peano.Term).varFinset) := by simp
    have hg := termVar_guard φ x (.var x) x hx hmem
    have hlt : x < guardBase A := by
      have hm := termVars_in_axiom_of_occurs φ x (.var x) hx hmem
      have hl : x ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) hm
      dsimp [guardBase]
      omega
    have hd := domainAt_transport (guardBase A) (x+1) x (by omega) (by omega)
    have hi := self_instance φ x
    change KDerivation (imp (guardFormula A).encode
      (imp (code (FOL.allAt x φ)) (code (FOL.substAt φ x (.var x)))))
    rw [PASoundness.SyntaxTransport.substAt_self]
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [code (FOL.allAt x φ), (guardFormula A).encode]
    have hA : Context Γ (code (FOL.allAt x φ)) := Context.head [_] _
    have hG : Context Γ (guardFormula A).encode := .hypothesis (by simp [Γ])
    exact .mp (.mp (.mp hG (.closed hg)) (.closed hd)) (.mp hA (.closed hi))
  · exact PASoundness.PAtoCompactVacuousAllElim.allElim_of_unused φ x (.var x) hx

theorem allElim_self_certificate (φ : Peano.Formula) (x : Nat) :
    theoremCode (certificate (allElim_self φ x)) =
      guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x (.var x))) := certificate_correct _

#print axioms PASoundness.PAtoCompactAllElimSelf.allAt_align_self
#print axioms PASoundness.PAtoCompactAllElimSelf.self_instance
#print axioms PASoundness.PAtoCompactAllElimSelf.allElim_self
#print axioms PASoundness.PAtoCompactAllElimSelf.allElim_self_certificate
end PASoundness.PAtoCompactAllElimSelf
