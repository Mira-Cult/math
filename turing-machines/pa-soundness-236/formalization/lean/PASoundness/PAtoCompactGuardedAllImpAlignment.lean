import PASoundness.PAtoCompactScopedActiveAll
import PASoundness.PAtoCompactGuardedGeneralizationAlignment

/-! A generated universal can be moved to a shared, genuinely fresh binder
and its body aligned with the translation under that binder. -/
namespace PASoundness.PAtoCompactGuardedAllImpAlignment

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactVacuousUniversal
open PASoundness.PAtoCompactVacuousUniversalFresh PASoundness.PAtoCompactScopedActiveAll

def originalChild (φ : Peano.Formula) (x : Nat) : Formula :=
  scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 (topName x φ))

def commonAll (φ : Peano.Formula) (x z : Nat) : Formula :=
  .all z (.imp (domainAt (z+1) z)
    (scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 z)))

/-- Actual finite K proof data aligning a translated PA universal with the
same source body under a shared fresh binder. No arithmetic soundness is used. -/
noncomputable def align_at (φ : Peano.Formula) (x z : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names) :
    KBoth (formula (FOL.allAt x φ)) (commonAll φ x z) := by
  let body := allAtBody x φ
  let old := topName x φ
  let child := originalChild φ x
  have hs : Fin.snoc (α := fun _ : Fin 1 => Nat) Fin.elim0 old (0 : Fin 1) = old := by
    exact congrFun (Fin.snoc_zero (Fin.elim0 : Fin 0 → Nat) old) (0 : Fin 1)
  have hn : old ∉ body.freeVarFinset := by
    intro h
    have hl := free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 old (by
      change old ∈ (allAtBody x φ).freeVarFinset
      exact h)
    exact Nat.lt_irrefl old hl
  have hbind : old ∉ child.binders := by
    have h := active_not_binder body (Fin.snoc Fin.elim0 old) (0 : Fin 1)
    simpa [hs, child, originalChild, body, old] using h
  have hguard : z ∉ (.imp (domainAt (z+1) old) child : Formula).names := by
    simp only [Formula.names, Finset.mem_union, not_or]
    exact ⟨low_name_not_domain_names (z+1) old z (by omega) (by omega), hz⟩
  have hreplace := scoped_active_replace body (Fin.snoc Fin.elim0 old) (0 : Fin 1) z
    (by simpa [hs] using hn) (by simpa [hs, old] using hgt)
    (by simpa [child, originalChild, body, old] using hz)
  have henv : (rename old z ∘ Fin.snoc Fin.elim0 old) = Fin.snoc Fin.elim0 z := by
    funext i
    fin_cases i
    simp [rename, Fin.snoc]
  have hchild : KBoth (replace old z child)
      (scopedFormula 1 body (Fin.snoc Fin.elim0 z)) := by
    simpa only [hs, henv, child, originalChild, body, old] using hreplace
  have hr := raw_rebase old (z+1) child (by omega)
  have ha := raw_high_alpha old z (z+1) child (by omega) (by omega) hbind hguard
  have hforward := allCongr z (implicationCongr (identity (domainAt (z+1) z).encode) hchild.1)
  have hbackward := allCongr z (implicationCongr (identity (domainAt (z+1) z).encode) hchild.2)
  change KBoth (rawGuard old child) (commonAll φ x z)
  exact ⟨compose hr.1 (compose ha.forward hforward),
    compose hbackward (compose ha.backward hr.2)⟩

end PASoundness.PAtoCompactGuardedAllImpAlignment

#print axioms PASoundness.PAtoCompactGuardedAllImpAlignment.align_at
