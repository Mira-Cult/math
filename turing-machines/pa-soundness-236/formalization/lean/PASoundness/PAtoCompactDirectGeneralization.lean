import PASoundness.PAtoCompactScopedBindSelf
import PASoundness.PAtoCompactScopedActiveAll
import PASoundness.PAtoCompactGeneralizationConditional

/-! Guarded generalization in the finite K calculus, using the proved
same-name binding alignment and active-name replacement. -/
namespace PASoundness.PAtoCompactDirectGeneralization

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGeneralizationConditional PASoundness.PAtoCompactGeneralizationGuardAssembly
open PASoundness.PAtoCompactGuardedVacuity PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactScopedActiveAll PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactGuardBaseTransport

@[simp] theorem snoc_zero (j : Nat) : (@Fin.snoc 0 (fun _ => Nat) Fin.elim0 j 0) = j := @Fin.snoc_last 0 (fun _ => Nat) j Fin.elim0

/-- The same-name binding interface, realized below for every PA formula. -/
structure BindSelf where
  align : ∀ φ : Peano.Formula, ∀ x : Nat,
    KBoth (formula φ) (scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 x))

def scopeAt (φ : Peano.Formula) (x j : Nat) : Formula :=
  scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 j)

def commonFresh (φ : Peano.Formula) (x : Nat) : Nat :=
  max x (max (topName x φ) (((scopeAt φ x x).names ∪
    (scopeAt φ x (topName x φ)).names).sup id)) + 1

/-- Compose guarded generalization in the finite K calculus. The intermediate
name `w` allows both source and target binders to be changed safely, including
when the source name equals the allocated target name. -/
noncomputable def generalization (h : BindSelf) (x : Nat) (φ : Peano.Formula)
    (d : KDerivation (guardedCode φ)) : KDerivation (guardedCode (FOL.allAt x φ)) := by
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
  have halpha := raw_align x z w (w+1) Tx Tz hxw hzw (by omega) hxb hzb hwTx hwTz hc
  have hpre : KDerivation (imp (guardFormula (FOL.allAt x φ)).encode (guardedBody φ x).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt (extraBase φ x) x).encode, (guardFormula (FOL.allAt x φ)).encode]
    have hg : Context Γ (guardFormula (FOL.allAt x φ)).encode := .hypothesis (by simp [Γ])
    have hx : Context Γ (domainAt (extraBase φ x) x).encode := .hypothesis (by simp [Γ])
    have hh : Context Γ (guardFormula φ).encode := .mp hx (.mp hg (.closed (guard_assemble φ x)))
    exact .mp hh (.closed d)
  have hxnot : x ∉ (FOL.allAt x φ).freeVarFinset := by
    simp [PASoundness.SyntaxTransport.allAt_freeVars]
  have hall : KDerivation (imp (guardFormula (FOL.allAt x φ)).encode
      (allCode x (guardedBody φ x).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply generalizeOne x (guardFormula_vacuity (FOL.allAt x φ) x hxnot)
    exact .mp (Context.head [] _) (.closed hpre)
  have hd : KDerivation (imp (domainAt (x+1) x).encode (domainAt (extraBase φ x) x).encode) :=
    domainAt_transport (x+1) (extraBase φ x) x (by omega) (by unfold extraBase; omega)
  have hh := allCongr x (implicationCongr hd (h.align φ x).1)
  have hg := compose hall (compose hh halpha.1)
  simpa only [guardedCode, code_allAt, rawGuard, Formula.encode, z, Tz, scopeAt, topBody] using hg

noncomputable def actualBindSelf : BindSelf where
  align φ x := by
    have h := PASoundness.PAtoCompactScopedBindSelf.scoped_bind_self φ x Fin.elim0
    have he : (Fin.append (fun _ : Fin 1 => x) (Fin.elim0 : Fin 0 → Nat)) = Fin.snoc Fin.elim0 x := by
      funext i
      fin_cases i
      simp [Fin.append, Fin.addCases]
    have hb : PASoundness.PAtoCompactScopedUnusedLevel.bindName x =
        (fun y : Nat => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) := rfl
    rw [hb, he] at h
    exact h

noncomputable def generalization_unconditional (x : Nat) (φ : Peano.Formula)
    (d : KDerivation (guardedCode φ)) : KDerivation (guardedCode (FOL.allAt x φ)) :=
  generalization actualBindSelf x φ d

theorem generalization_unconditional_certificate (x : Nat) (φ : Peano.Formula)
    (d : KDerivation (guardedCode φ)) :
    theoremCode (certificate (generalization_unconditional x φ d)) =
      guardedCode (FOL.allAt x φ) := certificate_correct _

#print axioms PASoundness.PAtoCompactDirectGeneralization.generalization
#print axioms PASoundness.PAtoCompactDirectGeneralization.actualBindSelf
#print axioms PASoundness.PAtoCompactDirectGeneralization.generalization_unconditional
#print axioms PASoundness.PAtoCompactDirectGeneralization.generalization_unconditional_certificate
end PASoundness.PAtoCompactDirectGeneralization
